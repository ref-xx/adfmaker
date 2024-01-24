/*
 * Copyright (C) 2024 Alessandro Gatti - frob.it
 *
 * SPDX-License-Identifier: Apache-2.0
 */

//! Rust equivalents for selected Amiga OS data structures.

use std::{fmt, str::FromStr};

use chrono::{DateTime, Duration, TimeZone, Utc};
use encoding::{all::ISO_8859_1, EncoderTrap, Encoding};
use log::{debug, error};
use memoize::memoize;

use crate::common::Error;

#[doc(hidden)]
macro_rules! report_bcpl_string_error {
    ($name:expr, $cause:expr) => {
        error!("Invalid BCPL string \"{}\": {}.", $name, $cause);
    };

    ($name:expr, $cause:expr, $($field:expr),+) => {
        error!("Invalid BCPL string \"{}\": {}.", $name, format!($cause, $($field),+));
    };
}

/// The two states the `Delete` bit can have in a [`ProtectionBits`] instance.
#[derive(Clone, Debug, PartialEq)]
pub(crate) enum DeleteBit {
    /// The file or directory can be deleted.
    Allowed,
    /// The file or directory can not be deleted.
    NotAllowed,
}

/// The two states the `Execute` bit can have in a [`ProtectionBits`] instance.
#[derive(Clone, Debug, PartialEq)]
pub(crate) enum ExecuteBit {
    /// The file can be executed.
    Allowed,
    /// The file can not be executed.
    NotAllowed,
}

/// The two states the `Write` bit can have in a [`ProtectionBits`] instance.
#[derive(Clone, Debug, PartialEq)]
pub(crate) enum WriteBit {
    /// The file or directory can be written to.
    Allowed,
    /// The file or directory can not be written to.
    NotAllowed,
}

/// The two states the `Read` bit can have in a [`ProtectionBits`] instance.
#[derive(Clone, Debug, PartialEq)]
pub(crate) enum ReadBit {
    /// The file or directory can be read from.
    Allowed,
    /// The file or directory can not be read from.
    NotAllowed,
}

/// The two states the `Changed` bit can have in a [`ProtectionBits`] instance.
#[derive(Clone, Debug, PartialEq)]
pub(crate) enum ChangeBit {
    /// The file or directory has not changed since the last backup.
    NotChanged,
    /// The file or directory has changed since the last backup.
    Changed,
}

/// DOS longword type indicating a metadata block.
pub(crate) const T_SHORT: u32 = 2;
/// DOS longword type indicating a file data container block.
pub(crate) const T_DATA: u32 = 8;
/// DOS longword type indicating a file data index extension list block.
pub(crate) const T_LIST: u32 = 16;
/// DOS longword secondary type for the root directory block.
pub(crate) const ST_ROOT: u32 = 1;
/// DOS longword secondary type for directory blocks besides the root.
pub(crate) const ST_USERDIR: u32 = 2;
/// DOS longword secondary type for file blocks.
pub(crate) const ST_FILE: u32 = 0xFFFF_FFFD;

/// `BCPL` string wrapper.
///
/// Amiga OS's DOS structures use `BCPL` strings, which are just `ISO-8859-1`
/// encoded strings prepended by a single-byte length marker.  In other words,
/// what are nowadays known as `Pascal`-type strings.
///
/// [Wikipedia](https://en.wikipedia.org/wiki/AmigaDOS) provides more
/// information on the link between `BCPL` and Amiga OS.
#[derive(Clone, Debug, Default)]
pub(crate) struct BCPLString(String);

impl fmt::Display for BCPLString {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{}", self.0)
    }
}

impl PartialEq for BCPLString {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl FromStr for BCPLString {
    type Err = Error;

    /// Convert the given string into an owned `BCPLString` instance.
    ///
    /// This is the only supported method to create a `BCPLString` out of a
    /// series of characters, as it performs all the necessary checks to make
    /// sure the input data can be represented as a `BCPLString` instance.
    ///
    /// # Errors
    ///
    /// If the input string cannot be represented as a `BCPL` string, either
    /// [`Error::BCPLStringTooLong`] or [`Error::InvalidStringEncoding`]
    /// will be returned.  The former if the input string length cannot be
    /// represented in a single [`u8`], the latter if the input data contains
    /// characters that aren't present in the `ISO 8859-1` character set.
    fn from_str(string: &str) -> Result<Self, Self::Err> {
        if string.len() >= (u8::MAX as usize) {
            return Err(Error::BCPLStringTooLong {
                string: string.to_owned().into(),
                length: string.len(),
            });
        }

        if let Err(error) = ISO_8859_1.encode(string, EncoderTrap::Strict) {
            return Err(Error::InvalidStringEncoding {
                string: string.to_owned().into(),
                reason: error,
            });
        }

        Ok(Self(string.to_owned()))
    }
}

impl BCPLString {
    /// Create a byte-level representation of the `BCPLString` instance.
    ///
    /// This function builds a [`Vec<u8>`] containing a ready to be serialised
    /// representaton of the [`BCPLString`] instance it is called on.  The
    /// output [`Vec<u8>`] can be serialised as it is, since it matches how
    /// Amiga OS stores `BCPL` strings in memory.
    pub(crate) fn to_vec(&self) -> Vec<u8> {
        // Building a BCPL string from anything but `BCPLString::from_str` is
        // not supported.  Both string length and encoding are checked in that
        // function, so the two unchecked unwraps here are guaranteed to
        // succeed.

        assert!(
            self.0.len() < u8::MAX as usize,
            "Invalid BCPL string length (max {}, got {}).",
            u8::MAX,
            self.0.len()
        );

        #[allow(clippy::cast_possible_truncation)]
        let length = self.0.len() as u8;
        [
            vec![length; 1],
            ISO_8859_1.encode(&self.0, EncoderTrap::Strict).unwrap(),
        ]
        .concat()
    }

    /// Extracts a string slice containing the entire underlying [`String`].
    pub(crate) fn as_str(&self) -> &str {
        self.0.as_str()
    }
}

/// Create a `BCPL` string with additional validation criteria.
///
/// This function will create a `BCPL` string out of the given [`&str`] checking
/// whether its length is not more than a specific threshold, that the input
/// string won't contain any character from a given banned characters list, and
/// that the input value could be represented as an `ISO-8859-1` string.
///
/// # Errors
///
/// If any of the criteria mentioned above are not met, the function will return
/// [`Error::InvalidBCPLString`].
pub(crate) fn build_bcpl_string(
    string: &str,
    maximum_length: usize,
    invalid_characters: Option<&[char]>,
) -> Result<BCPLString, Error> {
    debug!("Checking string \"{}\" for BCPL compliance.", string);

    if let Some(invalid_characters) = invalid_characters {
        for invalid_character in invalid_characters {
            if string.contains(*invalid_character) {
                report_bcpl_string_error!(
                    string,
                    "invalid character '{}' found in string",
                    *invalid_character
                );
                return Err(Error::InvalidBCPLString {
                    string: string.to_owned().into(),
                    reason: format!("Invalid character '{invalid_character}' found in string.")
                        .into(),
                });
            }
        }
    }

    if string.len() >= maximum_length {
        report_bcpl_string_error!(
            string,
            "string \"{}\" too long (max {}, got {} characters)",
            maximum_length,
            string,
            string.len()
        );
        return Err(Error::InvalidBCPLString {
            string: string.to_owned().into(),
            reason: format!(
                "String \"{string}\" too long: (max {maximum_length}, got {}).",
                string.len()
            )
            .into(),
        });
    }

    debug!("String \"{}\" can be a valid BCPL string.", string);

    BCPLString::from_str(string)
}

/// Return the Amiga OS epoch timestamp.
///
/// Amiga OS uses January 1st, 1978 at midnight as its epoch.  However it is not
/// specified which time zone it is supposed to be used with said epoch.  For
/// the sake of simplicity, it is assumed that the epoch timestamp is based on
/// the UTC time zone.
#[memoize]
fn get_amiga_epoch() -> DateTime<Utc> {
    // No error handling here, as if this fails the situation cannot be
    // recovered (cannot build `DateStamp` instances without a starting epoch),
    // hence a panic is enough.

    Utc.with_ymd_and_hms(1978, 1, 1, 0, 0, 0).single().unwrap()
}

/// Create a byte-level representation of the given [`Duration`] instance.
///
/// This function builds a [`Vec<u8>`] containing a ready to be serialised
/// representaton of the passed [`Duration`] instance.  The output [`Vec<u8>`]
/// can be serialised as it is, since it matches how Amiga OS stores
/// [`DateStamp`] instances in memory.
#[memoize]
fn delta_to_vec(delta: Duration) -> Vec<u8> {
    // No error handling here, as the check on whether the number of days fits
    // in an `i32` is done when building the `Duration` instance.  Minutes and
    // milliseconds are already bounded by modulo operations, and hence they can
    // be safely unwrapped.

    [
        #[allow(clippy::cast_possible_truncation)]
        (delta.num_days() as i32).to_be_bytes(),
        #[allow(clippy::cast_possible_truncation)]
        ((delta.num_minutes() % (24 * 60)) as i32).to_be_bytes(),
        #[allow(clippy::cast_possible_truncation)]
        (((delta.num_milliseconds() % 1000) / 2) as i32).to_be_bytes(),
    ]
    .iter()
    .flat_map(|bytes| *bytes)
    .collect()
}

/// `DateStamp` timestamp wrapper.
///
/// Amiga OS represents timestamps in an unique way.  It still keeps track of
/// time instants as the distance between a chosen epoch (midnight of January
/// 1st, 1978) like other operating systems out there, but the in-memory
/// representation is not seen anywhere else.
///
/// Rather than storing the {milli,micro}seconds from an arbitrary point in
/// time, what is stored is the amount of days from the epoch, then the number
/// of minutes from midnight, and finally the amount of "ticks" (1/50th of a
/// second).  This may not be as space efficient as other operating systems, but
/// it was safe from [the Y2K issue](https://en.wikipedia.org/wiki/Y2K_problem)
/// compliant from the get-go, and also sidesteps
/// [the Y2038 issue](https://en.wikipedia.org/wiki/Year_2038_problem) too,
/// whilst using 32-bit integers. Considering Amiga OS was developed in the
/// early 1980s, that was quite forward-thinking.
#[derive(Clone, Debug)]
pub(crate) struct DateStamp {
    epoch_delta: Duration,
}

impl Default for DateStamp {
    fn default() -> Self {
        Self {
            epoch_delta: Duration::zero(),
        }
    }
}

impl DateStamp {
    /// Convert the given timestamp into a [`DateStamp`] instance.
    ///
    /// This is the only supported method to create a [`DateStamp`] out of a
    /// timestamp instance, as it performs all the necessary checks to make
    /// sure the input data can be represented as a [`DateStamp`] instance.
    ///
    /// # Errors
    ///
    /// If the input timestamp cannot be represented as a [`DateStamp`]
    /// instance, [`Error::TimestampRepresentation`] will be returned.  This
    /// only occurs whether the given timestamp is more than 2<sup>31</sup> days
    /// away from the epoch (in either direction).
    pub(crate) fn from_utc(date_time: DateTime<Utc>) -> Result<Self, Error> {
        let epoch_delta = date_time - get_amiga_epoch();

        if i32::try_from(epoch_delta.num_days()).is_err() {
            return Err(Error::TimestampRepresentation(date_time));
        }

        Ok(Self {
            epoch_delta: date_time - get_amiga_epoch(),
        })
    }

    /// Create a byte-level representation of the [`DateStamp`] instance.
    ///
    /// This function builds a [`Vec<u8>`] containing a ready to be serialised
    /// representaton of the [`DateStamp`] instance it is called on.  The output
    /// [`Vec<u8>`] can be serialised as it is, since it matches how Amiga OS
    /// stores [`DateStamp`] strings in memory.
    pub(crate) fn to_vec(&self) -> Vec<u8> {
        // The `memoize` crate cannot memoize struct functions, so we use a
        // trampoline function to achieve the same effect.
        delta_to_vec(self.epoch_delta)
    }
}

impl fmt::Display for DateStamp {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{}", get_amiga_epoch() + self.epoch_delta)
    }
}

/// Amiga file object protection bits.
///
/// This is a collection of five flags representing the access permissions that
/// filesystem objects can have in Amiga OS OFS.  The permission bits are:
///
/// - Changed: if set, the file was changed since the last backup, not really
///            used except for backup applications
/// - Read: if set, the file or directory can be read from by Amiga OS
/// - Write: if set, the file or directory can be written to by Amiga OS
/// - Execute: if set, the file can be executed by Amiga OS
/// - Delete: if set, the file or directory can be deleted by Amiga OS.
///
/// By default, [`ProtectionBits`] instances represent an Amiga OS filesystem
/// object that has not changed since the last backup, can be read from, can be
/// written to, can be executed, and can be deleted.
///
/// Since protection bits are serialised to disk as a 32-bits longword, a
/// convenience function to convert an instance to an [`u32`] is provided.
#[derive(Clone, Debug)]
pub(crate) struct ProtectionBits {
    changed: ChangeBit,
    read: ReadBit,
    write: WriteBit,
    execute: ExecuteBit,
    delete: DeleteBit,
}

impl From<ProtectionBits> for u32 {
    fn from(bits: ProtectionBits) -> Self {
        u32::from(&bits)
    }
}

impl From<&ProtectionBits> for u32 {
    fn from(bits: &ProtectionBits) -> Self {
        let mut value = u32::from(bits.changed == ChangeBit::NotChanged) << 4;
        value |= u32::from(bits.read == ReadBit::NotAllowed) << 3;
        value |= u32::from(bits.write == WriteBit::NotAllowed) << 2;
        value |= u32::from(bits.execute == ExecuteBit::NotAllowed) << 1;
        value |= u32::from(bits.delete == DeleteBit::NotAllowed);

        value
    }
}

impl Default for ProtectionBits {
    fn default() -> Self {
        Self {
            changed: ChangeBit::Changed,
            read: ReadBit::Allowed,
            write: WriteBit::Allowed,
            execute: ExecuteBit::Allowed,
            delete: DeleteBit::Allowed,
        }
    }
}

impl fmt::Display for ProtectionBits {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "----{}{}{}{}",
            if self.read == ReadBit::Allowed {
                "r"
            } else {
                "-"
            },
            if self.write == WriteBit::Allowed {
                "w"
            } else {
                "-"
            },
            if self.execute == ExecuteBit::Allowed {
                "e"
            } else {
                "-"
            },
            if self.delete == DeleteBit::Allowed {
                "d"
            } else {
                "-"
            },
        )
    }
}

impl fmt::UpperHex for ProtectionBits {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{:08X}", u32::from(self))
    }
}

impl FromStr for ProtectionBits {
    type Err = Error;

    /// Converts the given string into a [`ProtectionBits`] instance.
    ///
    /// The string format must look something like `----RWED`, with the first
    /// four characters being `-`, and the last four be either the ones shown or
    /// a `-` to indicate the permission is not granted.  The permissions are
    /// `R` (read), `W` (write), `E` (execute), `D` (delete) and must show up in
    /// that specific order, not caring for text case.
    ///
    /// This is the very same format permissions are displayed by enumerating
    /// Amiga OS directories from the command line interface, if the appropriate
    /// parameters are passed to `dir`.
    ///
    /// If the format is incorrect, [`Error::InvalidProtectionBitsString`] is
    /// returned instead.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// # use amigaostypes::ProtectionBits;
    /// # use common::Error;
    /// # fn main() -> Result<(), Error> {
    /// assert_eq!("----rw-d", ProtectionBits::from_str("----Rw-D")?.display());
    /// # }
    /// ```
    fn from_str(string: &str) -> Result<Self, Self::Err> {
        if string.is_empty() {
            return Ok(Self::default());
        }

        let trimmed = string.trim().to_lowercase();
        if trimmed.len() != 8 || !trimmed.starts_with("----") {
            return Err(Error::InvalidProtectionBitsString(string.to_owned()));
        }

        let mut characters = trimmed[4..trimmed.len()].chars();

        let read = match characters.nth(0).unwrap() {
            'r' => ReadBit::Allowed,
            '-' => ReadBit::NotAllowed,
            _ => return Err(Error::InvalidProtectionBitsString(string.to_owned())),
        };

        let write = match characters.nth(0).unwrap() {
            'w' => WriteBit::Allowed,
            '-' => WriteBit::NotAllowed,
            _ => return Err(Error::InvalidProtectionBitsString(string.to_owned())),
        };

        let execute = match characters.nth(0).unwrap() {
            'e' => ExecuteBit::Allowed,
            '-' => ExecuteBit::NotAllowed,
            _ => return Err(Error::InvalidProtectionBitsString(string.to_owned())),
        };

        let delete = match characters.nth(0).unwrap() {
            'd' => DeleteBit::Allowed,
            '-' => DeleteBit::NotAllowed,
            _ => return Err(Error::InvalidProtectionBitsString(string.to_owned())),
        };

        Ok(ProtectionBits {
            changed: ChangeBit::Changed,
            read,
            write,
            execute,
            delete,
        })
    }
}
