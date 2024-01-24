/*
 * Copyright (C) 2024 Alessandro Gatti - frob.it
 *
 * SPDX-License-Identifier: Apache-2.0
 */

//! Functions for parsing input file lists.

use std::{collections::HashSet, fmt, fs::File, io::Read, path::PathBuf, str::FromStr};

use chrono::{DateTime, Utc};
use csv::StringRecord;
use log::{debug, error};

use crate::{
    amigaostypes::{build_bcpl_string, BCPLString, DateStamp, ProtectionBits},
    common::{Error, MAXIMUM_COMMENT_LENGTH, MAXIMUM_FILE_SIZE, MAXIMUM_NAME_LENGTH},
};

#[doc(hidden)]
macro_rules! report_parse_error {
    ($line:expr, $cause:expr) => {
        error!("Record parse failed at line {}: {}.", $line, $cause);
    };

    ($line:expr, $cause:expr, $($field:expr),+) => {
        error!("Record parse failed at line {}: {}.", $line, format!($cause, $($field),+));
    };
}

/// Preprocessed disk content file entry.
#[derive(Clone, Default)]
pub(crate) struct DiskEntry {
    /// The target path on the disk image.
    target_path: String,
    /// An optional [`PathBuf`] pointing to the entry data source.
    source_path: Option<PathBuf>,
    /// An optional comment string, as a [`BCPLString`] instance.
    comment: Option<BCPLString>,
    /// An optional set of permissions, as a [`ProtectionBits`] instance.
    protection_bits: Option<ProtectionBits>,
    /// An optional timestamp, as a ['DateStamp`] instance.
    timestamp: Option<DateStamp>,
    /// An optional [`Vec<u8>`] with file data read from disk.
    contents: Option<Vec<u8>>,
}

impl fmt::Display for DiskEntry {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "{} -> {} ({} bytes)",
            self.source_path
                .as_ref()
                .map_or("N/A".to_owned(), |path| path.display().to_string()),
            self.target_path,
            self.contents
                .as_ref()
                .map_or("N/A".to_owned(), |contents| contents.len().to_string())
        )
    }
}

impl DiskEntry {
    /// Get the disk entry's target path components.
    pub(crate) fn path_components(&self) -> Vec<&str> {
        self.target_path
            .split('/')
            .filter(|component| !component.is_empty())
            .collect()
    }

    /// Get the disk entry's comment, if any is present.
    pub(crate) fn comment(&self) -> Option<BCPLString> {
        self.comment.clone()
    }

    /// Get the disk entry's protection bits, if any are present.
    pub(crate) fn protection_bits(&self) -> Option<ProtectionBits> {
        self.protection_bits.clone()
    }

    /// Get the disk entry's timestamp, if any is present.
    pub(crate) fn timestamp(&self) -> Option<DateStamp> {
        self.timestamp.clone()
    }

    /// Get the disk entry's target path.
    pub(crate) fn target_path(&self) -> &str {
        self.target_path.as_str()
    }

    /// Get the disk entry's source path.
    pub(crate) fn source_path(&self) -> Option<PathBuf> {
        self.source_path.clone()
    }

    /// Get the disk entry's contents size, if any are present.
    pub(crate) fn size(&self) -> Option<u32> {
        #[allow(clippy::cast_possible_truncation)]
        self.contents.as_ref().map(|contents| contents.len() as u32)
    }

    /// Get the disk entry's contents, if any are present.
    pub(crate) fn contents(&self) -> Option<&[u8]> {
        self.contents.as_deref()
    }
}

/// Process the input path to remove stray path separators.
///
/// Usually a function like this should also resolve `.` and `..` directories
/// by respectively strip the path segment and remove the previous path segment.
/// However, on Amiga OS, those path segment names are perfectly valid names, so
/// there is no need to strip those.
///
/// # Errors
///
/// The function will return [`Error::InvalidTargetFileName`] if the input file
/// path cannot represent an Amiga OS path name.
///
/// # Examples
///
/// ```no_run
/// # use filelist;
/// # use common::Error;
/// # fn main() -> Result<(), Error> {
/// assert_eq!("/a/b/c/d".to_owned(), normalise_target_path("//a///b/c//d/")?);
/// # }
/// ```
fn normalise_target_path(path: &str) -> Result<String, Error> {
    debug!("Normalising path \"{}\".", path);

    let mut path_fragments: Vec<&str> = vec![];

    for fragment in path.split('/') {
        if fragment.is_empty() {
            continue;
        }

        match build_bcpl_string(fragment, MAXIMUM_NAME_LENGTH, Some(&[':'])) {
            Ok(_) => path_fragments.push(fragment),
            Err(error) => {
                return Err(Error::InvalidTargetFileName {
                    name: path.to_owned().into(),
                    reason: format!("Fragment \"{fragment}\" cannot be a BCPL string: {error}.",)
                        .into(),
                })
            }
        };
    }

    debug!("Path normalised into: \"/{}\".", path_fragments.join("/"));

    Ok(format!("/{}", path_fragments.join("/")))
}

/// Bind the given wrapped `CSV` record to its line number.
///
/// # Errors
///
/// The function will return [`Error::InvalidFileList`] if the file entry line
/// is invalid.
fn unwrap_record(
    wrapped_record: &Result<StringRecord, csv::Error>,
) -> Result<(u64, &StringRecord), Error> {
    match wrapped_record {
        Ok(record) => {
            let line = if let Some(position) = record.position() {
                position.line()
            } else {
                error!("Record has no attached line number.");
                return Err(Error::InvalidFileList {
                    line: 0,
                    reason: "Record has no attached line number.".into(),
                });
            };

            Ok((line, record))
        }

        Err(error) => {
            let line = if let Some(position) = error.position() {
                report_parse_error!(position.line(), error);
                position.line()
            } else {
                error!("Record parse failed: {}.", error);
                0
            };
            Err(Error::InvalidFileList {
                line,
                reason: error.to_string().into(),
            })
        }
    }
}

/// Parse the target path field of a file entry `CSV` line.
///
/// # Errors
///
/// The function will return [`Error::InvalidFileList`] if the file name is
/// invalid.
fn parse_target_path(field: Option<&str>, line: u64) -> Result<String, Error> {
    if let Some(path) = field {
        let wrapped_name = normalise_target_path(path);
        if let Err(error) = wrapped_name {
            report_parse_error!(line, "cannot normalise target path \"{}\"", path);
            return Err(Error::InvalidFileList {
                line,
                reason: format!("Cannot parse target path: {error}.").into(),
            });
        }
        Ok(wrapped_name.unwrap())
    } else {
        report_parse_error!(line, "target path missing");
        Err(Error::InvalidFileList {
            line,
            reason: "Target path missing in record.".into(),
        })
    }
}

/// Parse the source path field of a file entry `CSV` line.
///
/// # Errors
///
/// The function will return [`Error::InvalidFileList`] if the file name is
/// invalid.
fn parse_source_path(field: Option<&str>, line: u64) -> Result<Option<(PathBuf, Vec<u8>)>, Error> {
    if let Some(path) = field {
        if path.is_empty() {
            return Ok(None);
        }
        let wrapped_path_buffer = PathBuf::from_str(path).unwrap().canonicalize();
        if let Err(error) = wrapped_path_buffer {
            report_parse_error!(line, "cannot canonicalise source path \"{}\"", path);
            return Err(Error::InvalidFileList {
                line,
                reason: format!("Cannot canonicalise source path: {error}").into(),
            });
        }

        // Reading a file at a later stage may theoretically trigger a denial of
        // service if the input file is changed between this instant and the
        // moment the file is opened and read from.  Thus, the file data is read
        // upfront rather than on-demand.

        let wrapped_file = File::open(wrapped_path_buffer.as_ref().unwrap());
        if let Err(error) = wrapped_file {
            report_parse_error!(line, "cannot open source path \"{}\"", path);
            return Err(Error::InvalidFileList {
                line,
                reason: format!("Cannot open source path: {error}").into(),
            });
        }
        let mut file = wrapped_file.unwrap();
        let wrapped_metadata = file.metadata();
        if let Err(error) = wrapped_metadata {
            report_parse_error!(line, "cannot acquire metadata for source path \"{}\"", path);
            return Err(Error::InvalidFileList {
                line,
                reason: format!("Cannot acquire metadata for source path: {error}").into(),
            });
        }
        let metadata = wrapped_metadata.unwrap();
        if !metadata.is_file() {
            report_parse_error!(line, "source path \"{}\" is not a file", path);
            return Err(Error::InvalidSourcePath(path.to_owned()));
        }
        let size = metadata.len();
        if size > MAXIMUM_FILE_SIZE {
            report_parse_error!(
                line,
                "source path file \"{}\" too big ({} bytes).",
                path,
                size
            );
            return Err(Error::InvalidFileList {
                line,
                reason: format!("Source path {path} is too large ({size} bytes).").into(),
            });
        }

        debug!(
            "Using source path \"{}\" containing {} bytes.",
            wrapped_path_buffer.as_ref().unwrap().display(),
            size
        );

        // `size` here is guaranteed to fit in an `usize`.
        #[allow(clippy::cast_possible_truncation)]
        let mut buffer: Vec<u8> = vec![0u8; size as usize];
        file.read_exact(&mut buffer)?;
        Ok(Some((wrapped_path_buffer.unwrap().clone(), buffer)))
    } else {
        debug!("No source path provided.");
        Ok(None)
    }
}

/// Parse the comment field of a file entry `CSV` line.
///
/// # Errors
///
/// The function will return [`Error::InvalidFileList`] if the file comment is
/// invalid.
fn parse_comment(field: Option<&str>, line: u64) -> Result<Option<BCPLString>, Error> {
    if let Some(comment_string) = field {
        let wrapped_comment = build_bcpl_string(comment_string, MAXIMUM_COMMENT_LENGTH, None);
        if let Err(error) = wrapped_comment {
            report_parse_error!(line, "invalid comment found \"{}\"", error);
            return Err(Error::InvalidFileList {
                line,
                reason: format!("Comment cannot be encoded: {error}.").into(),
            });
        }

        Ok(Some(wrapped_comment.unwrap()))
    } else {
        Ok(None)
    }
}

/// Parse the protection bits field of a file entry `CSV` line.
///
/// # Errors
///
/// The function will return [`Error::InvalidFileList`] if the file protection
/// bits are invalid.
fn parse_protection_bits(field: Option<&str>, line: u64) -> Result<Option<ProtectionBits>, Error> {
    match field {
        Some(bits) => {
            let wrapped_bits = ProtectionBits::from_str(bits);
            if let Err(error) = wrapped_bits {
                report_parse_error!(line, "cannot parse protection bits: {}", error);
                return Err(Error::InvalidFileList {
                    line,
                    reason: format!("Cannot parse protection bits: {error}.").into(),
                });
            }

            Ok(Some(wrapped_bits.unwrap()))
        }
        None => Ok(None),
    }
}

/// Parse the timestamp field of a file entry `CSV` line.
///
/// # Errors
///
/// The function will return [`Error::InvalidFileList`] if the file timestamp
/// is invalid.
fn parse_timestamp(field: Option<&str>, line: u64) -> Result<Option<DateStamp>, Error> {
    match field {
        Some(string) => {
            if string.is_empty() {
                return Ok(Some(DateStamp::default()));
            }

            let wrapped_timestamp = DateTime::parse_from_rfc3339(string);
            if let Err(error) = wrapped_timestamp {
                report_parse_error!(line, "cannot parse timestamp: {}", error);
                return Err(Error::InvalidFileList {
                    line,
                    reason: format!("Cannot parse timestamp: {error}.").into(),
                });
            }

            let wrapped_datestamp =
                DateStamp::from_utc(wrapped_timestamp.unwrap().with_timezone(&Utc));
            if let Err(error) = wrapped_datestamp {
                report_parse_error!(line, "cannot convert timestamp: {}", error);
                return Err(Error::InvalidFileList {
                    line,
                    reason: format!("Cannot convert timestamp: {error}.").into(),
                });
            }

            Ok(Some(wrapped_datestamp.unwrap()))
        }
        None => Ok(None),
    }
}

/// Read a list of file entries from the `CSV` file backed by the given reader.
///
/// This function will parse lines coming out of the given reader as `CSV` rows,
/// skipping the first one (meant to be used as header).  `CSV` rows must have
/// five fields each, described as such:
///
/// - target file name
/// - optional source file name (mandatory for files, optional for directories)
/// - optional comment
/// - optional [protection bits](ProtectionBits)
/// - optional timestamp in
///   [RFC3339 format](https://www.rfc-editor.org/rfc/rfc3339.html)
///
/// Valid entry rows are then wrapped into [`DiskEntry`] structurs, meant to be
/// added to a disk image via [`crate::DiskImageBuilder::add_entry`].
///
/// # Errors
///
/// The function will return [`Error::InvalidFileList`] if one or more entries
/// are invalid.
pub(crate) fn read_file_list<R>(reader: &mut R) -> Result<Vec<DiskEntry>, Error>
where
    R: Read,
{
    let mut csv_reader = csv::Reader::from_reader(reader);
    let mut names_set: HashSet<String> = HashSet::new();
    let mut entries: Vec<DiskEntry> = vec![];
    let mut seen_prefixes: Vec<String> = vec![];

    // target, [source], [comment], [protection], [timestamp]

    for file_entry in csv_reader.records() {
        let (line, record) = unwrap_record(&file_entry)?;

        if record.len() > 5 {
            report_parse_error!(line, "too many fields ({})", record.len());
            return Err(Error::InvalidFileList {
                line,
                reason: "Stray fields found.".into(),
            });
        }

        let target_path = parse_target_path(record.get(0), line)?;
        debug!("Found target path: \"{}\"", target_path);
        let normalised_name = target_path.to_lowercase();
        if names_set.contains(&normalised_name) {
            report_parse_error!(line, "duplicated file entry \"{}\"", target_path);
            return Err(Error::InvalidFileList {
                line,
                reason: format!("Duplicated file entry \"{target_path}\".").into(),
            });
        }
        for seen_prefix in &seen_prefixes {
            if normalised_name.starts_with(seen_prefix) {
                return Err(Error::InvalidFileList {
                    line,
                    reason: format!(
                        "File entry target path \"{target_path}\" assumes \"{seen_prefix}\" is a directory."
                    ).into(),
                });
            }
        }
        names_set.insert(normalised_name);
        let (source_path, contents) =
            if let Some((source_path, contents)) = parse_source_path(record.get(1), line)? {
                (Some(source_path), Some(contents))
            } else {
                (None, None)
            };

        let entry = DiskEntry {
            target_path,
            source_path,
            comment: parse_comment(record.get(2), line)?,
            protection_bits: parse_protection_bits(record.get(3), line)?,
            timestamp: parse_timestamp(record.get(4), line)?,
            contents,
        };

        if entry.source_path.as_ref().is_some() {
            seen_prefixes.push(format!("{}/", entry.target_path.to_lowercase().clone()));
        }
        entries.push(entry);
    }

    Ok(entries)
}
