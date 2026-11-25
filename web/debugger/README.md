# hevm's debugger page

The page of hevm's interactive debugger, formerly hevm-web-ui. The website opens it in a
window of its own, where it debugs on `hevm-web.wasm`: replaying a counterexample, or a test
function symbolically. The website hands each window its session, and hands it again when the
window is reloaded, while the website is open.

It speaks hevm's JSON API (see `hevm test --interactive` in hevm's docs), so it can also
debug a native hevm:

```shell
hevm test --root <project> --match <test> --interactive    # serves on 127.0.0.1:7317
cd web && HEVM_DEBUGGER=http://127.0.0.1:7317 npm run dev  # then open /debugger/
```

`npm test` in `web/` runs its tests, which parse sample answers of the API in
`test/fixtures/`. After the API changes, `node fixtures.mjs [hevm]` rewrites them from a
running hevm debugger; it needs hevm and an SMT solver on PATH, e.g. in hevm's nix shell.

The code: `api.ts` (the API's schemas, and how requests reach hevm), `model.ts` (state,
pure), `view.ts` and `highlight.ts` (what the panes show, pure), `vdom.ts`, `keys.ts`,
and `app.ts`, the only module with side effects. Colours are all in `index.html`'s CSS.
`src/vendor/prism.js` is Prism, for highlighting Solidity (MIT, see
`src/vendor/LICENSE.prism`).

## Licence

AGPL-3.0, as hevm; see `LICENSE`. `src/vendor/prism.js` is MIT, see
`src/vendor/LICENSE.prism`.
