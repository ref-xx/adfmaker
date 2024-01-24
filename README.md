# An Amiga OFS Disk Image Builder

This tool only allows to build double density OFS disk images.  The main reason to not support FFS or high density images is to maximise compatiblity. Almost every Amiga machine was released with a double density floppy drive (except for the A4000), and FFS was introduced in AmigaOS 2.0 leaving A1000, A500, A500+, and A2000 models out (arguably the most popular ones).

This tool is not meant for interactive use or to modify existing images.  It was written to address a need to build Amiga disk images from a build script, with the disk images' content being already available and known to fit in the image.

Images built with this tool have been successfully used with Workbench 1.3 and [ADFLib](https://github.com/lclevy/ADFlib)'s `unadf` tool.

## Build instructions

This program requires a recent version of the Rust programming language being installed and properly configured.  It was developed using Rust 1.75.0.

Once the source code is checked out from Git, it can be built with

```bash
cargo build -r
```

and then run from that directory with

```bash
cargo run -r -- <arguments>
```

This can be installed with

```bash
cargo install --path .
```

and if your system search path variable is properly set up, this will be made available as `adfmaker`.

## Command line arguments

The tool accepts the following command line arguments:

`-o`/`--output-file` (MANDATORY)

This indicates the path for the ADF file being built.  **Existing files will be overwritten**.

`-d`/`--disk-name` (MANDATORY)

The name for the disk that should appear in Workbench when the disk is inserted or how to reference the disk filesystem in the AmigaOS CLI.  It can be up to 30 characters, must not contain either `/` or `:` characters, and the string must be convertible to a valid [ISO-8859-1](https://en.wikipedia.org/wiki/ISO/IEC_8859-1) string.

`-f`/`--file-list` (MANDATORY)

The path of a CSV file containing the list of files to add along with their metadata information.  The format is described in a later section.

`-b`/`--bootblock` (OPTIONAL)

The path of a file that contains M68k code that should be executed by the Kickstart ROM when the machine is booted from this disk.  This must be up to 1012 bytes long.

`-v`/`--verbose` (OPTIONAL)

Increase logging verbosity (can be passed multiple times), although it doesn't really provide much use to anyone who do not plan to mess with the code.

`-q`/`--quiet` (OPTIONAL)

Decrease logging verbosity (can be passed multiple times).

## File list format

The file list is a CSV file with with five columns and a header row (the first non-empty line, ignored).  The columns are as follows:

- target file name
- source file name (omitted for directories)
- comment
- protection bits
- timestamp in [RFC3339 format](https://www.rfc-editor.org/rfc/rfc3339.html)

Of these five fields, only the first one (target file name) must not be empty.  The other ones have default values.

The comment field is used to assign a string to either a file or directory that can be shown when listing a directory in AmigaOS' command line interface.

### Field limitations

#### Target file name

AmigaOS OFS file names can have up to 30 character for each path component.  Each component must be convertible to a valid [ISO-8859-1](https://en.wikipedia.org/wiki/ISO/IEC_8859-1) string and not contain the `:` character.

Intermediate directories found in file paths without an explicit entry will be created automatically.  So for example if adding a file that should be called `a/b/c/d.txt` on the image, directories `a`, `b`, and `c` will be created with no additional intervention.

#### Source file name

If present, this must point to either an absolute or relative path to a file.  If it points to a directory it will not recursively add its contents to the disk image.

Entries with no source file name are assumed to be empty directories to be created in the disk image.

#### Comment

Comments can be up to 80 characters long and if present must be convertible to a a valid [ISO-8859-1](https://en.wikipedia.org/wiki/ISO/IEC_8859-1) string.

#### Protection bits

If explicitly set, they must be a string containing 8 characters with the first 4 being `-`, followed by either the appropriate bit in the correct order or a dash.  The bits (in the expected order) are as follows:

- R: if set allows the OS to read from the file or directory.
- W: if set allows the OS to write to the file or directory.
- E: if set allows the OS to execute the file.
- D: if set allows the OS to delete the file or directory.

So for example `----RW-D` applied to a file means that the file can be read from, written to, deleted, but not executed.  Bit letters case is not important, and the default permissions bit set is `----RWED`.

## Known bugs

- Intermediate directories that are created automatically do not inherit the timestamp of the final entry they are parent of.

## Licences and Copyright

This program is released under the Apache 2.0 licence, available in the repository as `LICENCE.txt`.

Where it applies: Copyright 2024 Alessandro Gatti - frob.it
