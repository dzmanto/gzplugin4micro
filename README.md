# gzplugin4micro
The gzip plugin provides some functionality to open and save .gz files
such that .gz files can be processed as if they were text files. Other
text editors such as vim also provide such functionality.

* When micro opens a file, micro will check whether the suffix if that
  file is .gz. If that is the case, the header of the .gz file is
  parsed. If the magic numbers 0x1f 0x8b are found in the header of
  the file, it will be processed as a .gz file.

* Likewise, when micro saves a file, micro will again check the suffix
  of the filename. If the suffix is .gz, the contents of the text
  buffer will be compressed. Appropriate information about crc32 and
  text buffer length is appended.

## Installation

### Settings

Add this repo as a **pluginrepos** option in the **~/.config/micro/settings.json** file (it is necessary to restart the micro after this change):

```json
{
  "pluginrepos": [
      "https://raw.githubusercontent.com/dzmanto/gzplugin4micro/master/repo.json"
  ]
}
```

### Install

In your micro editor press **Ctrl-e** and run command:

```
> plugin install gzplugin
```

or run in your shell

```sh
micro -plugin install gzplugin
```
