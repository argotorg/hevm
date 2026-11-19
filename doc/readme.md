# hevm Book

The hevm book is built using `mdbook` and `yarn`. Known good versions of both
are included in the flake `devShell`.

## Building the book

From the repository root, enter the development shell and build the JavaScript
bundle before building the book:

```shell
nix develop
cd doc
yarn install --frozen-lockfile
yarn build
mdbook build
```

The generated `theme/highlight.js` bundle is ignored by Git. Generate it before
the first `mdbook build` or `mdbook serve` in a checkout. The documentation CI
also installs the locked dependencies and generates this bundle before building
the book.

## Running the mdBook server

After building the JavaScript bundle, serve the documentation locally by calling
the [`serve` command][mdbook-serve] from the `doc` directory:

```shell
mdbook serve
```

Alternatively it can be called from the root of the repository:

```shell
mdbook serve doc
```

[mdbook-serve]: https://rust-lang.github.io/mdBook/cli/serve.html

## Updating syntax highlighting

In order to highlight the Solidity code examples in the book we override
mdBook's built-in [highlight.js] with our own. Edit `theme/theme.js` and regenerate
the bundle using [yarn]:

```shell
yarn build
```

This compiles `theme/theme.js` into `dist/theme.js` and copies the minified output
to `theme/highlight.js`, where mdBook picks it up during the build. Commit the
source changes; the generated bundle is rebuilt locally and in CI.

[highlight.js]: https://highlightjs.org/
[Yarn]: https://yarnpkg.com/
