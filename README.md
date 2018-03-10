# IdrisTddNotes
What this program does is up to you!
## building
Run `make` from this directory to generate the IdrisTddNotes executable.
## adding dependencies
Once the library you'd like to use is installed, you can add it to the `opts` line in IdrisTddNotes.ipkg. Remember to include a leading `-p` for each library, so adding the `contrib` library would result in:
```
opts = "-p effects -p contrib"
```
If you use [idris-mode](https://github.com/idris-hackers/idris-mode) for Emacs, then you'll also want to add the library name to .dir-locals.el so that it will be loaded with the REPL process.
