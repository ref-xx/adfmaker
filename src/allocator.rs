/*
 * Copyright (C) 2024 Alessandro Gatti - frob.it
 *
 * SPDX-License-Identifier: Apache-2.0
 */

//! Disk blocks allocator functions.

use log::{debug, error, trace};

use crate::common::{self, Error, BLOCKS_PER_IMAGE};

/// The first block available for storing user data.
pub const FIRST_BLOCK: u32 = 2;
/// The last block that can be used to store user data.
#[allow(clippy::cast_possible_truncation)]
pub const LAST_BLOCK: u32 = common::BLOCKS_PER_IMAGE as u32;

/// Check whether the given block number is in range.
///
/// # Errors
///
/// If the block number is out of range, the function will return
/// [`Error::BitmapBlockOutOfRange`].
pub(crate) fn check_block_number(block_number: u32) -> Result<(), Error> {
    if !(FIRST_BLOCK..LAST_BLOCK).contains(&block_number) {
        error!("Block #{} is outside the disk image bounds.", block_number);
        return Err(Error::BitmapBlockOutOfRange(block_number));
    }

    Ok(())
}

/// Disk sector allocator.
pub(crate) struct BitmapAllocator {
    /// The map of allocated blocks.
    ///
    /// There are more space-efficient ways to handle this, but given the amount
    /// of data in question, an array of [`bool`]s is good enough.
    bits: [bool; common::BLOCKS_PER_IMAGE],
    /// How many blocks have not been allocated yet.
    available: usize,
}

impl BitmapAllocator {
    /// Create a new bitmap allocator for an empty image.
    ///
    /// The allocator will automatically reserve the boot, root, and bitmap
    /// metadata blocks.
    pub(crate) fn new() -> Self {
        let mut bits = [true; common::BLOCKS_PER_IMAGE];
        bits[common::ROOT_BLOCK_NUMBER as usize] = false;
        bits[common::BITMAP_BLOCK_NUMBER as usize] = false;
        Self {
            bits,
            // Exclude the boot block, the root block, and the bitmap block.
            available: BLOCKS_PER_IMAGE - (FIRST_BLOCK as usize) - 2,
        }
    }

    /// Scavenger blocks allocator, starting from a given block index.
    ///
    /// This function starts collecting blocks to allocate starting from the
    /// given block index, without any concern for filesystem fragmentation or
    /// disk seeks minimisation.  If it was not possible to claim enough blocks
    /// from the given block start index, the function will return [`None`].
    fn collect_free_blocks(&mut self, count: usize, first_block: u32) -> Option<Vec<u32>> {
        let mut blocks: Vec<u32> = vec![];
        let mut blocks_count = count;

        let mut start = first_block;

        trace!("{} block(s) left to allocate.", blocks_count);
        while blocks_count > 0 {
            trace!(
                "Scanning for a free available block starting from #{}.",
                start
            );

            let mut allocated_block: Option<u32> = None;

            for block_number in start..LAST_BLOCK {
                let index = block_number as usize;
                trace!(
                    "Looking at block #{}, state: {}.",
                    index,
                    if self.bits[index] {
                        "FREE"
                    } else {
                        "ALLOCATED"
                    }
                );

                if self.bits[index] {
                    trace!(
                        "Choosing block #{} for the allocation operation.",
                        block_number
                    );
                    allocated_block = Some(block_number);
                    break;
                }
            }

            // There is no wrap-around on purpose.  The main allocation strategy
            // is to place directory blocks in the middle of the image (right
            // after the bitmap block, one after another), and files' blocks
            // starting from the block after the boot block.  There are two
            // possible instances where `allocated_block` is not set: either
            // there are more than ~800 directories on a floppy disk, or most
            // blocks are already allocated from start to end and a file cannot
            // fit.  The second case should already be caught by an explicit
            // check for the number of available blocks, but if it doesn't due
            // to a programming error then there's this safety net in place.

            let new_block = allocated_block?;
            blocks.push(new_block);
            debug!(
                "Found a free block at #{} ({} blocks found so far).",
                new_block,
                blocks.len()
            );
            blocks_count -= 1;
            trace!("{} block(s) left to allocate.", blocks_count);
            start = new_block + 1;
            if start >= LAST_BLOCK {
                error!("End of bitmap data area reached.");
                return None;
            }
        }

        Some(blocks)
    }

    /// Allocate the given amount of blocks.
    ///
    /// This uses a scavenging block allocator, using an optional starting block
    /// index to claim blocks from.
    ///
    /// # Errors
    ///
    /// If the allocator fails to claim enough blocks, the function will return
    /// either [`Error::DiskFull`] in case it is known there are not enough
    /// free blocks at all, or [`Error::EndOfBitmapReached`] if there are
    /// enough free blocks in the image but not enough when using the chosen
    /// starting point.
    pub(crate) fn allocate_blocks(
        &mut self,
        count: usize,
        start: Option<u32>,
    ) -> Result<Vec<u32>, Error> {
        debug!(
            "Attempting to allocate {} block(s) starting from block #{}.",
            count,
            start.unwrap_or(FIRST_BLOCK)
        );

        if count == 0 {
            return Ok(vec![]);
        }

        trace!("{} available block(s).", self.available);
        if self.available < count {
            error!(
                "Cannot allocate {} block(s) ({} available).",
                count, self.available
            );
            return Err(Error::DiskFull);
        }

        let first_block = start.unwrap_or(FIRST_BLOCK);
        check_block_number(first_block)?;

        let Some(blocks) = self.collect_free_blocks(count, first_block) else {
            return Err(Error::EndOfBitmapReached);
        };
        assert_eq!(
            &count,
            &blocks.len(),
            "Allocated blocks count mismatch (expected {count}, got {}).",
            &blocks.len()
        );

        debug!("Allocating {} free block(s).", &blocks.len());

        for block_number in &blocks {
            let index = *block_number as usize;

            trace!(
                "Looking at block #{}, state: {}.",
                block_number,
                if self.bits[index] {
                    "FREE"
                } else {
                    "ALLOCATED"
                }
            );
            assert!(
                self.bits[index],
                "Free block #{block_number} was already allocated.",
            );
            trace!("Allocating block #{}.", block_number);
            self.bits[index] = false;
            self.available -= 1;
        }

        debug!("Allocated {} block(s).", count);

        Ok(blocks)
    }

    /// Serialise the allocation map to be written to disk.
    ///
    /// This serialises the blocks allocation map as a [`Vec<u8>`] that should
    /// be written as-is to the bitmap metadata block on the disk.  Data is
    /// meant to be stored to disk as a [`Vec<u32>`] with each [`u32`]s least
    /// significant byte representing the lowest block number for the longword.
    /// Even though the number of available blocks is divisible by
    /// [`u32::BITS`], the first two blocks (used for the boot block) are not
    /// considered when serialising the bitmap.
    pub(crate) fn to_vec(&self) -> Vec<u8> {
        self.bits
            .iter()
            .skip(FIRST_BLOCK as usize)
            .copied()
            .collect::<Vec<bool>>()
            .chunks(u32::BITS as usize)
            .flat_map(|bits| {
                let mut word: u32 = 0;
                for (position, value) in bits.iter().enumerate() {
                    if *value {
                        word |= 1u32 << position;
                    }
                }
                word.to_be_bytes()
            })
            .collect::<Vec<u8>>()
    }

    /// Get the state for the given block.
    ///
    /// # Errors
    ///
    /// If the block is out of range, the function will return
    /// [`Error::BitmapBlockOutOfRange`].
    pub(crate) fn is_block_set(&self, block: u32) -> Result<bool, Error> {
        check_block_number(block)?;
        trace!(
            "Looking at block #{}, state: {}.",
            block,
            if self.bits[block as usize] {
                "FREE"
            } else {
                "ALLOCATED"
            }
        );
        Ok(self.bits[block as usize])
    }
}
