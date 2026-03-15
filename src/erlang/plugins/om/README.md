om
=====

A rebar plugin for Henk Programming Language.

Build
-----

```
    $ rebar3 compile
```

Use
---

Add the plugin to your rebar config:

```
    {plugins, [
        {om, {git, "https://github.com/groupoid/om.git", {tag, "0.1.0"}}}
    ]}.
```

Then just call your plugin directly in an existing application:

```
    $ rebar3 om
    ===> Fetching om
    ===> Compiling om
```

Credits
-------

* Namdak Tonpa
