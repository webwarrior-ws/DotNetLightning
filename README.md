
## How to configure

Configuration will follow an usual semantics for ASP.NET Core web app.
That is, it will read in following order.

* Read `appsettings.json`

## Supported platforms

It should work on every OS if we build Secp256k1 for every platform (right now we only provide Linux binaries).

## TODO

* Refactor PeerChannelEncryptor to optimize performance (Probably by using byref-like-type and mutable state)
* Update `Channel.deriveOurDustLimitSatoshis`

