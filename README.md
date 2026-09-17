This document should be built with Typst 0.14 or above. Locally I built it with `typst 0.14.0 (0da01659)`, so at least that version is tested. 

The build command is simply: 
```
typst compile etale-main.typ
```
with no fancy parameters. Keep in mind that since the document is large, you need quite a lot of memory to compile it. (The maximum resident size during compilication on my device was 5.5GB.)

The following fonts are required to be installed: 
- New Computer Modern
- FandolSong
- Garamond-Math