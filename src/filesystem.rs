/*
 * Copyright (C) 2024 Alessandro Gatti - frob.it
 *
 * SPDX-License-Identifier: Apache-2.0
 */

//! Functions to manipulate the internal filesystem tree representation.

use std::{
    cell::RefCell,
    fmt,
    io::Read,
    rc::{Rc, Weak},
    str::FromStr,
};

use encoding::{all::ISO_8859_1, EncoderTrap, Encoding};
use log::{debug, trace};

use crate::{
    allocator::{FIRST_BLOCK, LAST_BLOCK},
    amigaostypes::{build_bcpl_string, BCPLString, DateStamp, ProtectionBits},
    common::{
        self, HASH_TABLE_BUCKETS, MAXIMUM_NAME_LENGTH,
        ROOT_BLOCK_NUMBER,
    },
    filelist::DiskEntry,
};

/// Enumeration to describe the types of nodes that can be built.
#[derive(Clone, Debug, PartialEq)]
pub(crate) enum NodeKind {
    /// The node in question is a directory (either intermediate or final).
    Directory,
    /// The node in question is a file.
    File,
}

impl fmt::Display for NodeKind {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "{}",
            match self {
                NodeKind::Directory => "Directory",
                NodeKind::File => "File",
            }
        )
    }
}

// TODO: Normalise this data structure and use a builder instead.

/// A filesystem object, can be either a file or a directory.
///
/// This structure is meant to be part of a n-ary tree, containing not only
/// references to parent and child nodes, but also associated payload data if
/// any is present.
#[derive(Clone)]
pub(crate) struct Node {
    /// A weak reference to the parent node.
    ///
    /// The parent reference is guaranteed to be retained even if it is a weak
    /// reference as the parent node keeps a strong reference onto the node
    /// being created, hence making sure that either nodes won't be collected
    /// unless explicitly requested.
    parent: RefCell<Weak<RefCell<Node>>>,

    /// A chained hash map containing children nodes.
    ///
    /// This must be left empty if the node is for a filesystem file object.
    children: ChainedHashMap,

    /// The Amiga OS protection bits for this filesystem node.
    protection_bits: ProtectionBits,

    /// The Amiga OS optional comment information for this filesystem node.
    comment: BCPLString,

    /// The filesystem node name.
    name: BCPLString,

    /// The filesystem node creation timestamp.
    timestamp: DateStamp,

    /// An optional payload container.
    payload: Option<DiskEntry>,

    /// The assigned disk block for this node.
    block: Option<u32>,
}

impl Node {
    /// Build an instance of a root filesystem node.
    pub(crate) fn root() -> Self {
        debug!("Allocating root filesystem node.");
        Self {
            parent: RefCell::new(Weak::new()),
            children: ChainedHashMap::new(HASH_TABLE_BUCKETS),
            protection_bits: ProtectionBits::default(),
            comment: BCPLString::default(),
            name: BCPLString::default(),
            timestamp: DateStamp::default(),
            payload: None,
            block: Some(ROOT_BLOCK_NUMBER),
        }
    }

    /// Build a new, empty filesystem node with the given name and parent.
    ///
    /// Most of the parameters for this constructor are empty and are meant to
    /// be filled in at a later stage when building the node tree.
    fn new(
        parent: &Rc<RefCell<Node>>,
        name: &BCPLString,
        comment: Option<&BCPLString>,
        protection_bits: Option<ProtectionBits>,
        timestamp: Option<DateStamp>,
        payload: &Option<DiskEntry>,
    ) -> Rc<RefCell<Self>> {
        debug!(
            "Allocating filesystem node \"{}/{}\" ({}).",
            parent.borrow().absolute_path(),
            name,
            payload
                .as_ref()
                .map_or("No payload".to_owned(), ToString::to_string)
        );
        let node = Self {
            parent: RefCell::new(Rc::downgrade(parent)),
            children: ChainedHashMap::new(HASH_TABLE_BUCKETS),
            protection_bits: protection_bits.unwrap_or_default(),
            comment: comment.unwrap_or(&BCPLString::default()).to_owned(),
            name: name.to_owned(),
            timestamp: timestamp.unwrap_or_default(),
            payload: payload.clone(),
            block: None,
        };

        let mut borrowed_parent = parent.borrow_mut();
        let child_node = Rc::new(RefCell::new(node));
        borrowed_parent.children.add_entry(&child_node);
        child_node.clone()
    }

    /// Find a direct child whose name matches the given string.
    ///
    /// This will search only for children one level deep, it will not recurse
    /// down.  The function will panic if an invalid name is given.
    fn find_child(&self, name: &str) -> Option<Rc<RefCell<Node>>> {
        self.children.find_entry(name)
    }

    /// Get the node's absolute path.
    pub(crate) fn absolute_path(&self) -> String {
        let mut fragments: Vec<BCPLString> = vec![self.name.clone()];

        let mut parent = self.parent.borrow().upgrade();
        while parent.is_some() {
            let unwrapped_parent = parent.unwrap();
            fragments.push(unwrapped_parent.borrow().name.clone());
            parent = unwrapped_parent.borrow().parent.borrow().upgrade();
        }

        fragments.reverse();
        fragments
            .iter()
            .map(BCPLString::as_str)
            .collect::<Vec<&str>>()
            .join("/")
            .clone()
    }

    /// Build a filesystem node from the given [`DiskEntry`].
    pub(crate) fn from_disk_entry(
        root: &Rc<RefCell<Node>>,
        disk_entry: &DiskEntry,
    ) -> Rc<RefCell<Self>> {
        debug!(
            "Building filesystem node from disk entry \"{}\" rooted at \"{}\".",
            disk_entry.target_path(),
            root.borrow().absolute_path()
        );

        let mut current = root.clone();
        for path_fragment in disk_entry.path_components() {
            debug!(
                "Path fragment \"{}\" with current node \"{}\"",
                path_fragment,
                current.borrow().absolute_path()
            );

            let found_node = current.borrow().find_child(path_fragment);
            current = if let Some(found_node) = found_node {
                found_node
            } else {
                Node::new(
                    &current,
                    &BCPLString::from_str(path_fragment).unwrap(),
                    None,
                    None,
                    None,
                    &None,
                )
            };
        }

        let mut borrowed_current = current.borrow_mut();
        borrowed_current.comment = disk_entry.comment().unwrap_or_default().clone();
        borrowed_current.protection_bits = disk_entry.protection_bits().unwrap_or_default();
        borrowed_current.timestamp = disk_entry.timestamp().unwrap_or_default();
        borrowed_current.payload = Some(disk_entry.clone());

        current.clone()
    }

    /// Assign a disk block to the node.
    ///
    /// This function will panic if the block number is either in the boot block
    /// area, is the bitmap block number, or if its number is past the end of
    /// the disk.
    pub(crate) fn set_block(&mut self, block: u32) {
        assert!(
            self.block.is_none(),
            "Path \"{}\" already has a block allocated (#{}).",
            self.absolute_path(),
            self.block.unwrap()
        );

        assert!(
            (FIRST_BLOCK..LAST_BLOCK).contains(&block) && block != common::BITMAP_BLOCK_NUMBER,
            "An invalid block number slipped by: {block}",
        );

        debug!("Assigning block #{} to \"{}\".", block, self.absolute_path());

        self.block = Some(block);
    }

    /// Get the node's assigned block number, if any.
    pub(crate) fn block(&self) -> Option<u32> {
        self.block
    }

    /// Get the node's parent, if any.
    ///
    /// If this node has a parent a reference-counted instance of the parent
    /// cell will be returned, with its reference count increased by one.
    pub(crate) fn parent(&self) -> Option<Rc<RefCell<Node>>> {
        self.parent.borrow().upgrade().clone()
    }

    /// Build an iterator iterating through the children nodes.
    ///
    /// This iterator will only iterate through direct children of the node, and
    /// will not recurse down.
    pub(crate) fn children(&self) -> impl Iterator<Item = &Rc<RefCell<Node>>> {
        assert!(
            self.kind() == NodeKind::Directory,
            "Children iterator requested on file node \"{}\".",
            self.absolute_path()
        );
        self.children.nodes_iter()
    }

    /// Get the filesystem node's payload, if any is present.
    pub(crate) fn payload(&self) -> Option<DiskEntry> {
        self.payload.clone()
    }

    /// Get the filesystem node's name.
    pub(crate) fn name(&self) -> &BCPLString {
        &self.name
    }

    /// Get the filesystem node's kind.
    pub(crate) fn kind(&self) -> NodeKind {
        if self.payload.as_ref().is_some() && self.payload.as_ref().unwrap().source_path().is_some()
        {
            NodeKind::File
        } else {
            NodeKind::Directory
        }
    }

    /// Build an iterator iterating through the children hash table buckets.
    pub(crate) fn hash_table_buckets(&self) -> impl Iterator<Item = &Vec<Rc<RefCell<Node>>>> {
        self.children.buckets_iter()
    }
}

/// Simple implementation of a chained hash map for filesystem nodes.
#[derive(Clone)]
struct ChainedHashMap {
    buckets: Vec<Vec<Rc<RefCell<Node>>>>,
}

impl ChainedHashMap {
    /// Build a chained hash map with the given amount of buckets.
    fn new(buckets: usize) -> Self {
        assert!(buckets > 0, "Invalid number of buckets: {buckets}.");
        let mut table: Vec<Vec<Rc<RefCell<Node>>>> = vec![];
        (0..buckets).for_each(|_| table.push(vec![]));

        Self { buckets: table }
    }

    /// Calculate the destination bucket for the given name.
    ///
    /// The hash function is taken from Commodore's own documentation, available
    /// from [BombJack](https://commodore.bombjack.org/amiga/amiga-books.htm),
    /// search for "``AmigaDOS`` Technical Referene Manual" *(sic)*.
    ///
    /// In short, the hash function converts the input name (encoded as
    /// ISO-8859-1) into uppercase and repeatedly applies the given function
    /// for each byte: `hash = ((hash * 13) + byte) & 0x7FF` with the name
    /// length in bytes as the initial hash value, using 32-bit longwords for
    /// each variable and ignoring overflows that may occur.  The hash bucket
    /// the given file name should be placed in is the result of the operation
    /// described earlier, modulo the number of buckets available.
    fn calculate_hash_for_name(&self, name: &[u8]) -> usize {
        assert!(
            u32::try_from(name.len()).is_ok(),
            "An invalid node name slipped by ({} bytes long).",
            name.len()
        );

        (name
            .bytes()
            // This call to `unwrap()` is already checked earlier.
            .fold(u32::try_from(name.len()).unwrap(), |hash, byte| {
                hash.wrapping_mul(13)
                    // This call to `unwrap()` cannot fail.
                    .wrapping_add(u32::from(byte.unwrap().to_ascii_uppercase()))
                    & 0x0000_07FF
            }) as usize)
            % self.buckets.len()
    }

    /// Add the given node to the hash map.
    ///
    /// No checks are done to avoid the same node appearing more than once in
    /// the map, same goes for the validity of most of the internal state of the
    /// node being added.  To retrieve a particular node look at
    /// [``ChainedHashMap::find_entry``], and for iterating through nodes with
    /// no order look at [``ChainedHashMap::nodes_iter``].
    fn add_entry(&mut self, node: &Rc<RefCell<Node>>) {
        let wrapped_name = ISO_8859_1.encode(node.borrow().name.as_str(), EncoderTrap::Strict);
        assert!(
            wrapped_name.is_ok(),
            "An invalid node name slipped by: \"{}\".",
            node.borrow().name
        );
        let bucket = self.calculate_hash_for_name(&wrapped_name.unwrap());
        self.buckets[bucket].push(node.clone());
    }

    /// Retrieves a child node whose name matches the given string.
    ///
    /// This function will return an optional cloned counted reference to the
    /// node matching the input string.
    fn find_entry(&self, name: &str) -> Option<Rc<RefCell<Node>>> {
        // Raising a panic here is fine, this function is not meant to be
        // invoked by anything but `Node`.
        let wrapped_name = build_bcpl_string(name, MAXIMUM_NAME_LENGTH, Some(&[':', '/']));
        assert!(
            wrapped_name.is_ok(),
            "An invalid node name slipped by: \"{name}\".",
        );
        let bcpl_name = wrapped_name.unwrap();

        // This call to `unwrap()` is checked earlier.
        self.buckets[self.calculate_hash_for_name(bcpl_name.as_str().as_bytes())]
            .iter()
            .find(|entry| entry.borrow().name == bcpl_name)
            .cloned()
    }

    // TODO: Figure out how to maintain reference counting without RefCell
    //       mutability capabilities for the nodes.

    /// Iterates through all the child nodes, in no specific order.
    ///
    /// The iterator allows for no explicit modification, as changes in the node
    /// name may change its destination bucket.
    fn nodes_iter(&self) -> impl Iterator<Item = &Rc<RefCell<Node>>> {
        self.buckets.iter().flatten()
    }

    /// Iterates through all the buckets that make up the hash map.
    ///
    /// The iterator allows for no explicit modification, as modification of
    /// contained nodes may change the nodes' destination bucket.
    fn buckets_iter(&self) -> impl Iterator<Item = &Vec<Rc<RefCell<Node>>>> {
        self.buckets.iter()
    }
}

/// Directory iterator to return directory nodes starting from a given root.
///
/// This iterator traverses the filesystem tree in-order.  Right now there is no
/// need to generalise this to return all nodes that match a certain criteria
/// set.
pub(crate) struct DirectoryIterator {
    stack: Vec<Rc<RefCell<Node>>>,
}

impl DirectoryIterator {
    /// Build a directory iterator starting from the given root node.
    pub(crate) fn new(root: &Rc<RefCell<Node>>) -> Self {
        debug!(
            "Building directory iterator starting at \"{}\".",
            root.borrow().absolute_path()
        );
        Self {
            stack: vec![root.clone()],
        }
    }
}

impl Iterator for DirectoryIterator {
    type Item = Rc<RefCell<Node>>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.stack.is_empty() {
            trace!("Stack is empty.");
        } else {
            trace!("Dumping stack entries:");
            for (index, entry) in self.stack.iter().enumerate() {
                trace!("Entry #{}: \"{}\".", index, entry.borrow().absolute_path());
            }
        }

        let Some(current) = self.stack.pop() else {
            debug!("References stack is empty, iterator consumed.");
            return None;
        };
        debug!(
            "Current element is now \"{}\".",
            current.borrow().absolute_path()
        );
        assert!(
            current.borrow().kind() == NodeKind::Directory,
            "A file was pushed onto the stack (\"{}\").",
            current.borrow().absolute_path()
        );

        let emitted = current.clone();

        debug!("Iterating through children.");
        for child in emitted.borrow().children() {
            debug!(
                "Found child: \"{}\", has payload: {}.",
                child.borrow().absolute_path(),
                if child.borrow().payload.is_some() {
                    "yes"
                } else {
                    "no "
                }
            );
            if child.borrow().kind() == NodeKind::Directory {
                debug!(
                    "{} directory node found, pushing it onto the stack.",
                    if child.borrow().payload.as_ref().is_none() {
                        "Intermediate"
                    } else {
                        "Final"
                    }
                );
                self.stack.push(child.clone());
                continue;
            }
        }
        debug!("Iteration finished.");

        Some(emitted)
    }
}
