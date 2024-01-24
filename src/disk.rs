/*
 * Copyright (C) 2024 Alessandro Gatti - frob.it
 *
 * SPDX-License-Identifier: Apache-2.0
 */

//! Lower level disk image manipulation functions.

use std::{
    cell::RefCell,
    collections::HashMap,
    fs::File,
    io::{self, Cursor, ErrorKind, Read, Write},
    mem,
    path::PathBuf,
    rc::Rc,
};

use log::{debug, error, trace, warn};
use pretty_hex::{HexConfig, PrettyHex};

use crate::{
    allocator::{check_block_number, BitmapAllocator},
    amigaostypes::{build_bcpl_string, BCPLString},
    common::{
        Error, BITMAP_BLOCK_NUMBER, BLOCKS_PER_IMAGE, DISK_BLOCK_LONGWORDS, DISK_BLOCK_SIZE,
        MAXIMUM_NAME_LENGTH, ROOT_BLOCK_NUMBER,
    },
    directories::{allocate_directories, build_root_block, write_directory_hash_table},
    filelist::DiskEntry,
    files::allocate_files,
    filesystem::{DirectoryIterator, Node},
};

/// The raw amount of bytes taken by the boot block.
const BOOT_BLOCK_SIZE: usize = DISK_BLOCK_SIZE * 2;

/// Read the boot block from the given path.
///
/// The function will return [`None`] if the given path points to a file that is
/// zero bytes in length, otherwise will return a [`Vec<u8>`] with the data read
/// from the file.
///
/// # Errors
///
/// The function will return [`Error::InputOutput`] if the input path does not
/// exist, is a directory, or a read error occurred when gathering the boot
/// block data.  If the file contains too much data,
/// [`Error::BootCodeTooLarge`] will be returned instead - no silent truncation
/// will take place.
fn read_boot_block(path: &PathBuf) -> Result<Option<Vec<u8>>, Error> {
    debug!("Opening boot code file: {}", path.display());
    let mut file = File::open(path)?;
    debug!("Boot code file opened.");
    let metadata = file.metadata()?;
    if !metadata.is_file() {
        error!("Boot code path does not point to a regular file.");
        return Err(Error::InputOutput(io::Error::new(
            ErrorKind::InvalidInput,
            "not a file",
        )));
    }
    debug!("Boot code file size: {} bytes.", metadata.len());
    if metadata.len() > (BOOT_BLOCK_SIZE - (mem::size_of::<u32>() * 3)) as u64 {
        error!(
            "Boot code file \"{}\" too big: {} bytes > {} bytes.",
            path.display(),
            metadata.len(),
            BOOT_BLOCK_SIZE - (mem::size_of::<u32>() * 3)
        );
        return Err(Error::BootCodeTooLarge(metadata.len()));
    }
    if metadata.len() == 0 {
        warn!("Boot code file is empty.");
        return Ok(None);
    }

    debug!("Reading boot code file.");
    #[allow(clippy::cast_possible_truncation)]
    let mut buffer: Vec<u8> = vec![0u8; metadata.len() as usize];
    file.read_exact(&mut buffer)?;
    debug!("Boot code file read.");

    Ok(Some(buffer))
}

/// Build a vaild Amiga DOS boot block with the given boot code, if any.
///
/// The boot block data is ready to be written to the disk image, with checksum
/// and all.
fn build_boot_block(boot_code: Option<Vec<u8>>) -> Vec<u8> {
    /*

     0                   1                   2                   3
     0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    |                  Header ("DOS")               |    0    |T|I|D|
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    |                            Checksum                           |
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    |                          Root block #                         |
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    |                                                               |
    +                          Boot code *                          +
    |                                                               |
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+

    T: 0 -> OFS, 1 -> FFS.
    I: 0 -> ISO-8859-1 filenames, 1 -> Other encoding for filenames.
    D: 0 -> Directory caching disabled, 1 -> Directory caching enabled.

    * Boot code entry not to scale.

    */

    // All calls to `unwrap()` are not checked, as those write operations are
    // guaranteed to succeed.  If they fail, either a bug in `Cursor` was hit
    // or the value of `BOOT_BLOCK_SIZE` is invalid.  In either case raising a
    // panic is the appropriate action, as there is no chance of recovery.

    let mut cursor = Cursor::new(vec![0u8; BOOT_BLOCK_SIZE]);
    cursor.write_all(&[b'D', b'O', b'S', 0]).unwrap();
    cursor.set_position((mem::size_of::<u32>() * 2) as u64);
    cursor.write_all(&ROOT_BLOCK_NUMBER.to_be_bytes()).unwrap();
    if let Some(boot_code) = boot_code {
        cursor.write_all(&boot_code).unwrap();
    }

    let mut block = cursor.into_inner();
    let mut checksum: u32 = 0;

    block
        .chunks_exact(mem::size_of::<u32>())
        .map(|chunk| u32::from_be_bytes(chunk.try_into().unwrap()))
        .for_each(|word| {
            let previous_checksum = checksum;
            checksum = checksum.wrapping_add(word);
            if checksum < previous_checksum {
                checksum = checksum.wrapping_add(1);
            }
        });

    (mem::size_of::<u32>()..)
        .zip((!checksum).to_be_bytes())
        .for_each(|(offset, byte)| block[offset] = byte);

    block
}

/// Calculate the effective offsets for a given longword index.
///
/// Longword offsets can be either positive or negative, with the former
/// representing longword offsets counted from the start of the block, and
/// the latter representing offsets computed from the end of the block.
///
/// This returns a tuple of three [`usize`] variables, containing the longword
/// index when counting from the beginning of the block, the longword index when
/// counting from the end of the block, and the effective offset in bytes of the
/// longword when starting from the end of the block.
///
/// The first two values are meant to be used for logging, whilst the last value
/// to be used for I/O seek operations.  This function panics if the longword
/// index is outside the disk block bounds.
///
/// # Examples
///
/// ```no_run
/// assert_eq!((0, 512, 0), calculate_longword_offset(0));
/// assert_eq!((511, 1, 2044), calculate_longword_offset(-1));
/// ```
fn calculate_longword_offset(offset: isize) -> (usize, usize, usize) {
    assert!(
        offset.unsigned_abs() < DISK_BLOCK_LONGWORDS,
        "Offset out of bounds: {offset}.",
    );

    let (forward_offset, backward_offset) = if offset >= 0 {
        (
            offset.unsigned_abs(),
            DISK_BLOCK_LONGWORDS - offset.unsigned_abs(),
        )
    } else {
        (
            DISK_BLOCK_LONGWORDS - offset.unsigned_abs(),
            offset.unsigned_abs(),
        )
    };

    (
        forward_offset,
        backward_offset,
        forward_offset * mem::size_of::<u32>(),
    )
}

/// Struct representing a single block that is part of an OFS disk image.
#[derive(Clone)]
pub(crate) struct DiskBlock {
    /// The block index.
    index: u32,
    /// The block contents.
    payload: [u8; DISK_BLOCK_SIZE],
}

impl DiskBlock {
    /// Create an empty disk block with the given index.
    ///
    /// # Errors
    ///
    /// The function will return [`Error::BitmapBlockOutOfRange`] if the index
    /// is past the range an OFS double density disk image allows.
    pub(crate) fn new(index: u32) -> Result<Self, Error> {
        check_block_number(index)?;

        Ok(Self {
            index,
            payload: [0u8; DISK_BLOCK_SIZE],
        })
    }

    /// Get the disk block index.
    pub(crate) fn index(&self) -> u32 {
        self.index
    }

    /// Get the disk block payload.
    ///
    /// To write in the payload bufffer, look at [`DiskBlock::write_longword`]
    /// and [`DiskBlock::write_buffer`].
    pub(crate) fn payload(&self) -> &[u8] {
        &self.payload
    }

    /// Write the given longword at a specific offset.
    ///
    /// Longword offsets can be either positive or negative, with the former
    /// representing longword offsets counted from the start of the block, and
    /// the latter representing offsets computed from the end of the block.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// # use disk::DiskBlock;
    /// # use common::Error;
    /// # use std::mem;
    /// # fn main() -> Result<(), Error> {
    /// let mut d = DiskBlock::new(0);
    /// d.write_longword(1, "forward", 0x12345678);
    /// assert_eq!(
    ///     d.payload()[std::mem::size_of::<u32>()] == 0x12 &&
    ///     d.payload()[std::mem::size_of::<u32>() + 1] == 0x34 &&
    ///     d.payload()[std::mem::size_of::<u32>() + 2] == 0x56 &&
    ///     d.payload()[std::mem::size_of::<u32>() + 3] == 0x78
    /// );
    /// d.write_longword(-1, "backward", 0x87654321);
    /// assert_eq!(
    ///     d.payload()[511 * std::mem::size_of::<u32>()] == 0x87 &&
    ///     d.payload()[511 * std::mem::size_of::<u32>() + 1] == 0x65 &&
    ///     d.payload()[511 * std::mem::size_of::<u32>() + 2] == 0x43 &&
    ///     d.payload()[511 * std::mem::size_of::<u32>() + 3] == 0x21
    /// );
    /// # }
    /// ```
    pub(crate) fn write_longword(&mut self, longword_offset: isize, name: &str, value: u32) {
        let (forward, backward, effective) = calculate_longword_offset(longword_offset);

        trace!(
            "Writing {} at longword {} (SIZE - {}) [effective offset ${:04X} ({})].",
            name,
            forward,
            backward,
            effective,
            effective
        );
        (effective..)
            .zip(value.to_be_bytes())
            .for_each(|(offset, byte)| self.payload[offset] = byte);
    }

    /// Read the longword located at a specific offset.
    ///
    /// Longword offsets can be either positive or negative, with the former
    /// representing longword offsets counted from the start of the block, and
    /// the latter representing offsets computed from the end of the block.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// # use disk::DiskBlock;
    /// # use common::Error;
    /// # use std::mem;
    /// # fn main() -> Result<(), Error> {
    /// let mut d = DiskBlock::new(0);
    /// d.write_longword(1, "forward", 0x12345678);
    /// assert_eq!(0x12345678, d.read_longword(1, "forward"));
    /// d.write_longword(-1, "backward", 0x87654321);
    /// assert_eq!(0x87654321, d.read_longword(-1, "backward"));
    /// # }
    /// ```
    pub(crate) fn read_longword(&self, longword_offset: isize, name: &str) -> u32 {
        let (forward, backward, effective) = calculate_longword_offset(longword_offset);

        trace!(
            "Reading {} at longword {} (SIZE - {}) [effective offset ${:04X} ({})].",
            name,
            forward,
            backward,
            effective,
            effective,
        );
        u32::from_be_bytes(
            self.payload[effective..(effective + mem::size_of::<u32>())]
                .try_into()
                .unwrap(),
        )
    }

    /// Write the given buffer into a specific offset.
    ///
    /// Longword offsets can be either positive or negative, with the former
    /// representing longword offsets counted from the start of the block, and
    /// the latter representing offsets computed from the end of the block.
    ///
    /// The buffer being written does not have to be longword-aligned.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// # use disk::DiskBlock;
    /// # use common::Error;
    /// # use std::mem;
    /// # fn main() -> Result<(), Error> {
    /// let mut d = DiskBlock::new(0);
    /// d.write_buffer(1, "forward", &[0x12u8, 0x34u8, 0x56u8, 0x78u8]);
    /// assert_eq!(
    ///     d.payload()[std::mem::size_of::<u32>()] == 0x12 &&
    ///     d.payload()[std::mem::size_of::<u32>() + 1] == 0x34 &&
    ///     d.payload()[std::mem::size_of::<u32>() + 2] == 0x56 &&
    ///     d.payload()[std::mem::size_of::<u32>() + 3] == 0x78
    /// );
    /// d.write_buffer(-1, "backward", &[0x87u8, 0x65u8, 0x43u8, 0x21u8]);
    /// assert_eq!(
    ///     d.payload()[511 * std::mem::size_of::<u32>()] == 0x87 &&
    ///     d.payload()[511 * std::mem::size_of::<u32>() + 1] == 0x65 &&
    ///     d.payload()[511 * std::mem::size_of::<u32>() + 2] == 0x43 &&
    ///     d.payload()[511 * std::mem::size_of::<u32>() + 3] == 0x21
    /// );
    /// # }
    /// ```
    pub(crate) fn write_buffer(&mut self, longword_offset: isize, name: &str, value: &[u8]) {
        let (forward, backward, effective) = calculate_longword_offset(longword_offset);

        trace!(
            "Writing {} at longword {} (SIZE - {}) [effective offset ${:04X} ({})].",
            name,
            forward,
            backward,
            effective,
            effective
        );

        (effective..)
            .zip(value)
            .for_each(|(offset, byte)| self.payload[offset] = *byte);
    }

    /// Calculate the block checksum.
    ///
    /// All OFS blocks with a checksum share the same algorithm (except for the
    /// Boot block and the Bitmap block); file and directory blocks always store
    /// said checksum at the same location (offset $14 of the block or longword
    /// #5).
    ///
    /// The checksum is simply the 32-bits 2's complement of the sum of all
    /// bytes present in the block.  For its correct calculation, this function
    /// must be run **before** the checksum is written to the disk block.  Leave
    /// the checksum field filled with zeroes before calling this function and
    /// it will just work.
    pub(crate) fn compute_checksum(&mut self) -> u32 {
        0u32.wrapping_sub(
            self.payload
                .chunks_exact(mem::size_of::<u32>())
                .map(|chunk| u32::from_be_bytes(chunk.try_into().unwrap()))
                .fold(0u32, u32::wrapping_add),
        )
    }

    /// Prepares an hex dump of the disk block image.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// # use disk::DiskBlock;
    /// # use common::Error;
    /// # use std::mem;
    /// # fn main() -> Result<(), Error> {
    /// let mut d = DiskBlock::new(0);
    /// d.write_longword(1, "longword", 0x12345678);
    /// d.dump().for_each(|line| println!("{line}"));
    /// # }
    /// ```
    pub(crate) fn dump(&self) -> Vec<String> {
        format!(
            "{:?}",
            self.payload.hex_conf(HexConfig {
                title: false,
                width: 8,
                group: 0,
                display_offset: 0,
                ..HexConfig::default()
            })
        )
        .lines()
        .map(ToOwned::to_owned)
        .collect::<Vec<String>>()
    }
}

/// Check whether the allocator state is consistent.
///
/// This functions will check whether the blocks that have been allocated so far
/// are marked as not available in the bitmap allocator's internal state.  If
/// that assumption does not hold true, this function will cause the application
/// to panic.
fn check_blocks_allocation_state(
    bitmap_allocator: &BitmapAllocator,
    blocks: &HashMap<u32, DiskBlock>,
) {
    for block in blocks.keys() {
        assert!(
            !bitmap_allocator.is_block_set(*block).unwrap(),
            "Disk block #{block} was built but not allocated.",
        );
    }
}

/// OFS Disk Image builder.
pub(crate) struct DiskImageBuilder {
    /// The disk name used by the operating system.
    name: BCPLString,
    /// An optional [`Vec<u8>`] with the data to put in the disk's boot block.
    boot_code: Option<Vec<u8>>,
    /// The filesystem node representing the root directory.
    root: Rc<RefCell<Node>>,
}

impl DiskImageBuilder {
    /// Create a [`DiskImageBuilder`] with no data.
    pub(crate) fn new() -> Self {
        Self {
            name: BCPLString::default(),
            boot_code: None,
            root: Rc::new(RefCell::new(Node::root())),
        }
    }

    /// Set the disk name.
    ///
    /// # Errors
    ///
    /// The function will return [`Error::InvalidDiskName`] if the given name
    /// is either too long, contains invalid characters (either `:` or `/`), or
    /// cannot be encoded as an `ISO-8859-1` string.
    pub(crate) fn set_name(&mut self, name: &str) -> Result<&mut Self, Error> {
        match build_bcpl_string(name, MAXIMUM_NAME_LENGTH, Some(&['/', ':'])) {
            Ok(name) => self.name = name,
            Err(error) => {
                return Err(Error::InvalidDiskName {
                    name: name.to_owned().into(),
                    reason: error.to_string().into(),
                })
            }
        };
        Ok(self)
    }

    /// Set the disk image's boot block.
    ///
    /// It is safe to pass an empty path, in that case nothing will be done, but
    /// if a boot block was previously set it **will not** be cleared.
    /// Functions in this builder are not meant to be called more than once.
    ///
    /// # Errors
    ///
    /// The function will return [`Error::InputOutput`] if there was an error
    /// reading the boot block file (as in, I/O read error, file not found,
    /// etc.), or [`Error::BootCodeTooLarge`] if the given file does not fit
    /// in the amount of space allocated for an OFS boot block.
    pub(crate) fn set_boot_block(&mut self, path: Option<PathBuf>) -> Result<&mut Self, Error> {
        if path.is_some() {
            self.boot_code = read_boot_block(&path.unwrap())?;
        }

        Ok(self)
    }

    /// Add the given [`DiskEntry`] to the disk image.
    ///
    /// This does **no checks** to make sure that the same file or directory is
    /// not added more than once to the filesystem tree.  Its purpose is to be
    /// called from a loop when the whole disk contents are already known and
    /// will not change.
    pub(crate) fn add_entry(&mut self, entry: &DiskEntry) -> &mut Self {
        debug!("Adding entry \"{}\" to the image.", entry.target_path());
        Node::from_disk_entry(&self.root, entry);
        self
    }

    /// Build the disk image.
    ///
    /// Creates a [`Vec<u8>`] containing the disk image data built with the
    /// settings given to the builder (disk name, files list, and an optional
    /// boot block payload).  Please note that calling this function invalidates
    /// the builder.
    ///
    /// # Errors
    ///
    /// This function will fail if there were problems building the boot block,
    /// the directory allocator failed, the file allocator failed.
    ///
    /// If the internal state became inconsistent, this function will cause the
    /// application to panic.  In that case there is no way to recover, hence
    /// the lack of more precise error handling.
    pub(crate) fn build(self) -> Result<Vec<u8>, Error> {
        // All calls to `unwrap()` on writes on `Cursor` are not checked, as
        // those write operations are guaranteed to succeed.  If they fail,
        // either a bug in `Cursor` was hit or the values of `BLOCKS_PER_IMAGE`
        // or `DISK_BLOCK_SIZE` are invalid.  In either case raising a panic is
        // the appropriate action, as there is no chance of recovery.

        let mut bitmap_allocator = BitmapAllocator::new();
        let mut cursor = Cursor::new(vec![0u8; BLOCKS_PER_IMAGE * DISK_BLOCK_SIZE]);
        cursor
            .write_all(&build_boot_block(self.boot_code.clone()))
            .unwrap();

        let mut blocks: HashMap<u32, DiskBlock> = HashMap::new();

        // Step 1. Build the root block with an empty hash table, no checksum,
        // but with everything else in its place.

        debug!("Building the root block.");
        blocks.insert(ROOT_BLOCK_NUMBER, build_root_block(&self.name, &self.root));
        check_blocks_allocation_state(&bitmap_allocator, &blocks);

        // TODO: Maybe a pluggable allocator could work here?  If image reading
        //       is added to the program this can become a disk defragmenter or
        //       an OFS ⇔ FFS converter.

        // TODO: Add a way to customise the file allocation order to optimise
        //       the disk layout for the application at hand.

        // Step 2. Allocate and build directory blocks with an empty hash table,
        // no checksum, detached from any other hash table, but with a valid
        // parent link.

        debug!("Allocating directories.");
        for directory_block in allocate_directories(&self.root, &mut bitmap_allocator)? {
            assert!(
                !blocks.contains_key(&directory_block.index()),
                "Disk block #{} seen more than once.",
                directory_block.index()
            );
            blocks.insert(directory_block.index(), directory_block);
        }
        debug!("Built {} block(s) so far.", blocks.len());
        check_blocks_allocation_state(&bitmap_allocator, &blocks);

        // Step 3. Allocate and build file blocks with fully formed data blocks,
        // header blocks detached from any other hash table and with no
        // checksum, but with a valid parent link.

        debug!("Allocating files.");
        for directory in DirectoryIterator::new(&self.root) {
            debug!("Adding files for \"{}\".", directory.borrow().absolute_path());
            for file_block in allocate_files(&directory, &mut bitmap_allocator)? {
                assert!(
                    !blocks.contains_key(&file_block.index()),
                    "Disk block #{} seen more than once.",
                    file_block.index()
                );
                blocks.insert(file_block.index(), file_block);
            }
        }
        debug!("Built {} block(s) so far.", blocks.len());
        check_blocks_allocation_state(&bitmap_allocator, &blocks);

        // Step 4. Once all nodes have a disk block assigned, the hash tables
        // can be written in, along with the chain pointers.

        debug!("Writing hash tables.");
        for directory in DirectoryIterator::new(&self.root) {
            write_directory_hash_table(&directory, &mut blocks);
        }
        debug!("Hash tables written.");
        check_blocks_allocation_state(&bitmap_allocator, &blocks);

        // Step 5. Compute checksums for all blocks, as all blocks built so far
        // need their checksum set at offset $14.

        debug!("Computing block checksums.");
        for block in blocks.values_mut() {
            let checksum = block.compute_checksum();
            block.write_longword(5, "checksum", checksum);
        }
        debug!("Block checksums computed.");
        check_blocks_allocation_state(&bitmap_allocator, &blocks);

        // Step 6. Build the bitmap block.

        debug!("Building the bitmap block.");

        // This call to `unwrap()` is not checked as if this fails there are
        // bigger problems to deal with.
        let mut bitmap_block = DiskBlock::new(BITMAP_BLOCK_NUMBER).unwrap();
        bitmap_block.write_buffer(1, "bitmap data", &bitmap_allocator.to_vec());
        let checksum = bitmap_block.compute_checksum();
        bitmap_block.write_longword(0, "checksum", checksum);
        assert!(
            !blocks.contains_key(&bitmap_block.index()),
            "Disk block #{} seen more than once.",
            bitmap_block.index()
        );
        blocks.insert(BITMAP_BLOCK_NUMBER, bitmap_block);
        check_blocks_allocation_state(&bitmap_allocator, &blocks);

        // Step 7. Put blocks where they belong.

        debug!("Writing blocks into the image.");
        for (index, block) in blocks {
            trace!(
                "Writing block #{} at offset ${:08X} ({}):",
                index,
                (index as usize) * DISK_BLOCK_SIZE,
                (index as usize) * DISK_BLOCK_SIZE
            );
            block.dump().iter().for_each(|line| trace!("{}", line));
            // The last block is at offset ~901000, so it will always fit in an
            // `u64`.
            cursor.set_position(((index as usize) * DISK_BLOCK_SIZE) as u64);
            cursor.write_all(block.payload()).unwrap();
        }
        debug!("Disk image built.");

        Ok(cursor.into_inner())
    }
}
