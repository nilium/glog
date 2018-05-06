glog
===

Leveled execution logs for Go.


Install
---

    $ go get -u go.spiff.io/glog


Usage
---

The comment from glog.go introduces the package:

> Package glog implements logging similar to the Google-internal C++
> INFO/ERROR/V setup.  It provides functions Info, Warning, Error, Fatal, plus
> formatting variants such as Infof. It also provides V-style logging,
> controlled by a logger's verbosity.
>
> This is a fork of the github.com/golang/glog package to remove global state
> (and specifically flagset dependency) from glog.
>
> Basic examples:
>
>     log := glog.NewLogger(glog.NewOptions())
>
>     log.Info("Prepare to repel boarders")
>
>     log.Fatalf("Initialization failed: %s", err)
>
> See the documentation for the V function for an explanation of these examples:
>
>     if log.V(2) != nil {
>         log.Info("Starting transaction...")
>     }
>
>     log.V(2).Infoln("Processed", nItems, "elements")

Unlike the original golang/glog package, this does not bind any specific
arguments to flag.CommandLine, nor does it have a global logger by default.


Notes
---

This is a fork of <https://github.com/golang/glog>. This repository is neither
supported or maintained by Google.


License
---

As with the original golang/glog package, this is licensed under the Apache-2.0 license.
A copy of the license can be found in the COPYING file.
