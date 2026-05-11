# SIP — Public OTA feed

Public Velopack-style release feed for the [Howard Medical SIP](https://github.com/Howard-Medical/SIPall) daemon and (eventually) E3 firmware. Source code lives in the private [Howard-Medical/SIPall](https://github.com/Howard-Medical/SIPall) monorepo; this repo holds only the build artifacts so that field-deployed Pi/Le Potato carts can pull updates without an embedded access token.

## How it works

Carts in the field poll **`daemon-manifest.json`** on this repo's `main` branch every 10 minutes (via `raw.githubusercontent.com`). The file is a tiny pointer:

```json
{
  "version": "1.0.41",
  "url":     "https://github.com/Howard-Medical/sip-releases/releases/download/daemon-v1.0.41/hmpd_python.py",
  "sha256":  "...",
  "gitTag":  "v1.0.41",
  "gitSha":  "9b0d1b1"
}
```

If the manifest version is newer than what the cart is running, the daemon downloads the script from the `url`, verifies the `sha256`, syntax-checks (`py_compile`), and atomically replaces itself.

## Per-release artifacts

Each tagged release here contains exactly one asset: `hmpd_python.py` (the daemon script). The `RELEASES` / `releases.win.json` / `.nupkg` files used by the Windows tool's Velopack feed live in a separate public repo at [Howard-Medical/TPLinkHotspot-releases](https://github.com/Howard-Medical/TPLinkHotspot-releases).

## Shipping a new version

1. Bump `SCRIPT_VERSION` in `daemon/hmpd_python.py` on `SIPall`, commit, tag.
2. Run `scripts/ota/build_ota_manifest.py --url=<release-asset-url>` on `SIPall`.
3. Upload `ota_staging/hmpd_python.py` here as a release asset.
4. Commit the updated `daemon-manifest.json` to this repo's `main`.
5. Carts pick up the new version on the next 10-min poll.

## Threat model

The manifest URL is a code constant in the daemon (env override was removed in v1.0.38). Anyone with write access to the Howard-Medical org can push a new manifest; the SHA256 in the manifest is *not* a signature, so the writer set IS the trust boundary. Signed manifests (Ed25519) are a planned future hardening.
