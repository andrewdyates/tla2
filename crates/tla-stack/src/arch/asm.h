// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

#if defined(APPLE) || (defined(WINDOWS) && defined(X86))
#define GLOBAL(name) .globl _ ## name; _ ## name
#else
#define GLOBAL(name) .globl name; name
#endif
