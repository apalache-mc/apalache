The landing page for Apalache served from http://informalsystems.github.io/apalache/

## Structure

### Landing site

The single landing page is generated from the [./index.md](./index.md) file. Make
a PR to edit that page if you need to fix/add/remove anything.

### Documentation

The documentation is built into HTML in the [./docs](./docs) directory. This is
done automatically by our CI system when new merges are made into either the
master or unstable branches. Do not edit those files by hand.

## Building locally

See the [github documentation for installation
instructions](https://docs.github.com/en/free-pro-team@latest/github/working-with-github-pages/testing-your-github-pages-site-locally-with-jekyll)

To build and run the site for local development:

``` sh
bundle exec jekyll serve
```
