# hevm-web-ui

A web page for [hevm](https://github.com/argotorg/hevm)'s interactive debugger.

hevm serves the debugger as a JSON API on localhost (`hevm test --interactive`, see
hevm's docs). This page is one client of it; `hevm-debug` is another.

## Running it

```shell
nix develop -c ./build.sh
hevm test --root <project> --match <test> --interactive    # in another terminal
nix develop -c node serve.mjs                           # then open http://127.0.0.1:7318
```

`serve.mjs` serves the page and passes its API calls on to hevm, so that the
browser sees one origin. `node serve.mjs <hevm port> <page port>` sets the ports
(7317 and 7318 by default).

## Developing

`nix develop -c ./build.sh test` type-checks and runs the tests. They parse
sample answers of the API in `test/fixtures/`. After hevm's API changes,
`node fixtures.mjs [hevm]` rewrites them from a running hevm debugger; it needs
hevm and an SMT solver on PATH, e.g. in hevm's nix shell.

The code: `api.ts` (the API's schemas), `model.ts` (state, pure), `view.ts` and
`highlight.ts` (what the panes show, pure), `vdom.ts`, `keys.ts`, and `app.ts`,
the only module with side effects. Colours are all in `index.html`'s CSS.
`src/vendor/prism.js` is Prism, for highlighting Solidity (MIT, see
`src/vendor/LICENSE.prism`).

## Licence

AGPL-3.0, as hevm; see `LICENSE`. `src/vendor/prism.js` is MIT, see
`src/vendor/LICENSE.prism`.
