/*
 * Copyright (C) 2024 Alessandro Gatti - frob.it
 *
 * SPDX-License-Identifier: Apache-2.0
 */

//! Directory-related filesystem manipulation functions.

use std::{cell::RefCell, collections::HashMap, rc::Rc};

use log::{debug, trace};

use crate::{
    allocator::{check_block_number, BitmapAllocator},
    amigaostypes::{BCPLString, DateStamp, ST_ROOT, ST_USERDIR, T_SHORT},
    common::{self, Error, BITMAP_BLOCK_NUMBER, HASH_TABLE_BUCKETS, ROOT_BLOCK_NUMBER},
    disk::DiskBlock,
    filesystem::{DirectoryIterator, Node, NodeKind},
};

/// Allocate disk blocks for all the directories found under the given root.
///
/// Since the root node by default is assigned block #880, this operates on all
/// *child* directories.  Blocks are placed just past the bitmap block, so from
/// block #882 and onwards.
///
/// The allocation procedure places all directories one after another in one
/// single, contiguous block, but can be improved by placing the file metadata
/// blocks for a given directory right after the directory metadata, so that
/// a breadth-first traversal will perform a series of contiguous reads.
/// Another improvement is to place directories at offset 0 of each track and
/// keeping the children file metadata data in the same track, spilling into the
/// same track but on the opposite side of the disk.
///
/// # Errors
///
/// The function will return [`Error::EndOfBitmapReached`] if there are no
/// free blocks to allocate, or [`Error::BitmapBlockOutOfRange`] if the
/// internal allocator state becomes inconsistent.
pub(crate) fn allocate_directories(
    root: &Rc<RefCell<Node>>,
    bitmap_allocator: &mut BitmapAllocator,
) -> Result<Vec<DiskBlock>, Error> {
    debug!("Allocating directory blocks.");

    let directory_blocks_count = DirectoryIterator::new(root).count() - 1;
    debug!(
        "Found {} directories (including root)",
        directory_blocks_count + 1
    );
    if directory_blocks_count == 0 {
        debug!("No non-root directories found.");
        return Ok(vec![]);
    }

    debug!("Allocating {} directory block(s).", directory_blocks_count);
    let mut directory_blocks =
        bitmap_allocator.allocate_blocks(directory_blocks_count, Some(BITMAP_BLOCK_NUMBER + 1))?;

    trace!(
        "Block(s) allocated: [{}].",
        directory_blocks
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<String>>()
            .join(", ")
    );
    directory_blocks.reverse();

    let mut blocks: Vec<DiskBlock> = vec![];

    for directory in DirectoryIterator::new(root) {
        trace!("Current directory: \"{}\".", directory.borrow().absolute_path());
        if directory.borrow().block().is_some() {
            debug!(
                "Directory \"{}\" already has block {} assigned.",
                directory.borrow().absolute_path(),
                directory.borrow().block().unwrap()
            );
            continue;
        }
        let directory_block = directory_blocks.pop();
        assert!(
            directory_block.is_some(),
            "Ran out of directory blocks before the directory iterator was consumed."
        );
        debug!(
            "Assigning block {} to directory \"{}\".",
            directory_block.unwrap(),
            directory.borrow().absolute_path()
        );
        let block = directory_block.unwrap();
        directory.borrow_mut().set_block(block);
        blocks.push(build_directory_block(block, &directory)?);
    }
    assert!(
        directory_blocks.is_empty(),
        "Directory iterator was consumed before running out of directory blocks."
    );

    Ok(blocks)
}

/// Create a root block from the given disk name and filesystem root node.
///
/// The root block created by this function will have an empty hash table (as in
/// no child nodes) and no checksum being set.  These fields should be filled in
/// at a later stage.
///
/// The function will perform **no checks** on the validity of the disk name,
/// and assumes it already honours length and content validity criteria.
pub(crate) fn build_root_block(disk_name: &BCPLString, root: &Rc<RefCell<Node>>) -> DiskBlock {
    debug!(
        "Building root block for disk \"{}\" at block #{}.",
        disk_name.as_str(),
        ROOT_BLOCK_NUMBER
    );

    trace!("Borrowing root filesystem node.");
    let borrowed_node = root.borrow();
    assert!(
        borrowed_node.parent().is_none(),
        "Filesystem node \"{}\" has a parent and is not the root node.",
        borrowed_node.absolute_path()
    );
    assert!(
        borrowed_node.kind() == NodeKind::Directory,
        "A file node \"{}\" slipped by.",
        borrowed_node.absolute_path()
    );

    /*

     0                   1                   2                   3
     0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    |                        Type ($00000002)                       | +0
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    |                                                               |
    +                               0 *                             + +1
    |                                                               |
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    |                        Hash table size                        | +3
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    |                                0                              | +4
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    |                         Block checksum                        | +5
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    |                                                               |
    +                      Hash table entries *                     + +6
    |                                                               |
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    |                       Bitmap valid flag                       | -50
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    |                                                               |
    +                   Bitmap pages block indices *                + -49
    |                                                               |
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    |                   Modification timestamp days                 | -23
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    |                 Modification timestamp minutes                | -22
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    |               Modification timestamp ticks (1/50s)            | -21
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    |  Name length  |                                               | -20
    +-+-+-+-+-+-+-+-+                                               +
    |                          Disk Name *                          |
    +                                                               +
    |                                                               |
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    |                     Creation timestamp days                   | -7
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    |                   Creation timestamp minutes                  | -6
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    |                 Creation timestamp ticks (1/50s)              | -5
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    |                                                               |
    +                               0 *                             + -4
    |                                                               |
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    |                   Secondary type ($00000001)                  | -1
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+

    * Block not to scale.

     */

    // This call to `unwrap()`` is not checked, as if it fails there are bigger
    // problems to deal with.
    let mut disk_block: DiskBlock = DiskBlock::new(ROOT_BLOCK_NUMBER).unwrap();
    disk_block.write_longword(0, "type", T_SHORT);
    #[allow(clippy::cast_possible_truncation)]
    disk_block.write_longword(3, "hash table size", common::HASH_TABLE_BUCKETS as u32);
    disk_block.write_longword(-50, "bitmap valid flag", 0xFFFF_FFFF);
    disk_block.write_longword(-49, "bitmap page block #", BITMAP_BLOCK_NUMBER);
    disk_block.write_buffer(
        -23,
        "modification timestamp",
        &DateStamp::default().to_vec(),
    );
    disk_block.write_buffer(-20, "disk name", &disk_name.to_vec());
    disk_block.write_buffer(-7, "creation timestamp", &DateStamp::default().to_vec());
    disk_block.write_longword(-1, "secondary type", ST_ROOT);

    trace!("Dumping root block in its current form:");
    disk_block.dump().iter().for_each(|line| trace!("{}", line));

    disk_block
}

/// Create a directory block for the given directory node and disk block number.
///
/// The directory block created by this function will have an empty hash table
/// (as in no child nodes), no checksum being set, and no parent node assigned.
/// These fields should be filled in at a later stage.
///
/// # Errors
///
/// The function will return [`Error::EndOfBitmapReached`] if there are no free
/// blocks to allocate, or [`Error::BitmapBlockOutOfRange`] if the chosen block
/// number is past the allowed disk blocks range.
pub(crate) fn build_directory_block(
    block_number: u32,
    node: &Rc<RefCell<Node>>,
) -> Result<DiskBlock, Error> {
    check_block_number(block_number)?;
    assert_eq!(
        NodeKind::Directory,
        node.borrow().kind(),
        "A file node \"{}\" slipped by.",
        node.borrow().absolute_path()
    );

    let borrowed_node = node.borrow();
    assert!(
        borrowed_node.parent().is_some(),
        "Filesystem node \"{}\" has no parent.",
        borrowed_node.absolute_path()
    );
    let borrowed_parent = borrowed_node.parent().unwrap();
    assert!(
        borrowed_parent.borrow().block().is_some(),
        "Filesystem node \"{}\"'s parent \"{}\" has no assigned block.",
        borrowed_node.absolute_path(),
        borrowed_parent.borrow().absolute_path(),
    );
    let payload = borrowed_node.payload().unwrap_or_default();
    assert!(
        payload.source_path().is_none(),
        "A file node \"{}\" slipped by.",
        borrowed_node.absolute_path()
    );

    /*

     0                   1                   2                   3
     0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    |                        Type ($00000002)                       | +0
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    |                          Own block #                          | +1
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    |                                                               |
    +                               0 *                             + +2
    |                                                               |
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    |                         Block checksum                        | +5
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    |                                                               |
    +                      Hash table entries *                     + +6
    |                                                               |
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    |                             Spare                             | -50
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    |                        Protection bits                        | -48
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    |                               0                               | -47
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    | Comment length|                                               | -46
    +-+-+-+-+-+-+-+-+                                               +
    |                         Comment data *                        |
    +                                                               +
    |                                                               |
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    |                    Creation timestamp days                    | -24
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    |                   Creation timestamp minutes                  | -23
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    |                Creation timestamp ticks (1/50s)               | -22
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    |  Name length  |                                               | -20
    +-+-+-+-+-+-+-+-+                                               +
    |                             Name *                            |
    +                                                               +
    |                                                               |
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    |      Next entry in hash chain (or 0 if this is the last)      | -4
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    |                         Parent block #                        | -3
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    |                               0                               | -2
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    |                   Secondary type ($00000002)                  | -1
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+

    * Block not to scale.

     */

    // This call to `unwrap()` is not checked, as the block number is already
    // checked by an earlier assertion.
    let mut disk_block = DiskBlock::new(block_number).unwrap();
    disk_block.write_longword(0, "type", T_SHORT);
    disk_block.write_longword(1, "own block #", block_number);
    disk_block.write_longword(
        -48,
        "protection bits",
        payload.protection_bits().unwrap_or_default().into(),
    );
    disk_block.write_buffer(
        -46,
        "comment",
        &payload.comment().unwrap_or_default().to_vec(),
    );
    disk_block.write_buffer(
        -23,
        "creation timestamp",
        &payload.timestamp().unwrap_or_default().to_vec(),
    );
    disk_block.write_buffer(-20, "directory name", &borrowed_node.name().to_vec());
    disk_block.write_longword(
        -3,
        "parent block pointer",
        borrowed_parent.borrow().block().unwrap(),
    );
    disk_block.write_longword(-1, "secondary type", ST_USERDIR);

    trace!("Dumping directory block in its current form:");
    disk_block.dump().iter().for_each(|line| trace!("{}", line));

    trace!("Releasing filesystem node.");
    Ok(disk_block)
}

/// Write the hash table for a given node.
///
/// This function will panic if the internal state of the hash table or of any
/// node contained becomes inconsistent.
pub(crate) fn write_directory_hash_table(
    node: &Rc<RefCell<Node>>,
    built_blocks: &mut HashMap<u32, DiskBlock>,
) {
    debug!("Writing hash table for \"{}\".", node.borrow().absolute_path());

    assert!(
        node.borrow().block().as_ref().is_some(),
        "Directory block \"{}\" has no assigned block number.",
        node.borrow().absolute_path()
    );

    assert!(
        built_blocks.contains_key(node.borrow().block().as_ref().unwrap()),
        "Filesystem directory node \"{}\" points to a block that was not built (#{}).",
        node.borrow().absolute_path(),
        node.borrow().block().as_ref().unwrap()
    );

    for (index, bucket) in node.borrow().hash_table_buckets().enumerate() {
        trace!(
            "Processing hash table bucket #{}, containing {} entries.",
            index,
            bucket.len()
        );

        if bucket.is_empty() {
            trace!("Bucket #{} is empty, skipping.", index);
            continue;
        }

        debug!(
            "Writing hash chain for bucket #{} of \"{}\".",
            index,
            node.borrow().absolute_path()
        );

        write_hash_chain(node, index, bucket, built_blocks);
    }
}

/// Build a hash chain link across members of the given bucket.
///
/// Even though the hash table already contains links between child entries and
/// their siblings in a given bucket, the contained nodes do not have any link
/// information that can be serialised onto the disk filesystem structure.
///
/// It is mandatory for all nodes traversed by this function to have a disk
/// block already assigned, otherwise it is not possible to build the link
/// between sibling nodes.
///
/// This function will panic if the internal state of the hash table or of any
/// node contained becomes inconsistent.
fn link_hash_chain(bucket: &[Rc<RefCell<Node>>], built_blocks: &mut HashMap<u32, DiskBlock>) {
    let mut iterator = bucket.iter().rev().peekable();

    loop {
        let wrapped_node = iterator.next();
        assert!(
            wrapped_node.as_ref().is_some(),
            "Unexpected bucket hash chain end reached."
        );
        let node = wrapped_node.unwrap().borrow();

        assert!(
            node.block().as_ref().is_some(),
            "Filesystem node \"{}\" has no assigned block.",
            node.absolute_path()
        );

        let node_block = node.block().unwrap();
        assert!(
            built_blocks.contains_key(&node_block),
            "Filesystem node \"{}\" points to a block that was not built (#{}).",
            node.absolute_path(),
            node_block
        );

        let next_wrapped_node = iterator.peek();
        if next_wrapped_node.as_ref().is_none() {
            break;
        }
        let next_node = next_wrapped_node.unwrap().borrow_mut();

        assert!(
            next_node.block().as_ref().is_some(),
            "Filesystem node \"{}\" has no assigned block.",
            next_node.absolute_path()
        );

        let next_node_block = next_node.block().unwrap();
        assert!(
            built_blocks.contains_key(&next_node_block),
            "Filesystem node \"{}\" points to a block that was not built (#{}).",
            next_node.absolute_path(),
            next_node_block
        );
        let next_node_disk_block = built_blocks.get_mut(&next_node_block).unwrap();

        debug!(
            "Creating link from \"{}\" (#{}) to \"{}\" (#{}).",
            node.absolute_path(),
            node_block,
            next_node.absolute_path(),
            next_node_block
        );

        next_node_disk_block.write_longword(-4, "hash chain pointer", node_block);
    }
}

/// Write the chain link information for a bucket into the node metadata blocks.
///
/// This function will panic if the internal state of the hash table or of any
/// node contained becomes inconsistent.
fn write_hash_chain(
    root: &Rc<RefCell<Node>>,
    bucket_index: usize,
    bucket: &[Rc<RefCell<Node>>],
    blocks: &mut HashMap<u32, DiskBlock>,
) {
    assert!(
        (0..HASH_TABLE_BUCKETS).contains(&bucket_index),
        "Invalid bucket index #{bucket_index}."
    );

    link_hash_chain(bucket, blocks);

    debug!("Chain built but disconnected from directory, creating link.");

    debug!(
        "Creating link from \"{}\" (#{}) to \"{}\" (#{}).",
        bucket[0].borrow().absolute_path(),
        bucket[0].borrow().block().as_ref().unwrap(),
        root.borrow().absolute_path(),
        root.borrow().block().as_ref().unwrap()
    );

    let root_disk_block = blocks.get_mut(&root.borrow().block().unwrap()).unwrap();
    assert!(
        root_disk_block.read_longword(
            isize::try_from(6 + bucket_index).unwrap(),
            format!("hash table bucket #{bucket_index}").as_str()
        ) == 0,
        "Hash table bucket #{bucket_index} for \"{}\" is not empty.",
        root.borrow().absolute_path()
    );
    root_disk_block.write_longword(
        isize::try_from(6 + bucket_index).unwrap(),
        format!("hash table bucket #{bucket_index}").as_str(),
        bucket[0].borrow().block().unwrap(),
    );

    debug!("All bucket chain links created.");
}
