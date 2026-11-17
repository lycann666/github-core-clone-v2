# forge — a GitHub-compatible git forge

A single-process GitHub-compatible git forge, written from scratch in
Python 3 standard library only. No dependencies, no git binary, no
outside service. It serves, from its own in-memory store:

- **git smart HTTP** (`/{owner}/{repo}.git`) — `git-upload-pack`
  protocol v2 (ls-refs, fetch with shallow/deepen, thin-pack) and
  `git-receive-pack` v0, with SHA-1 packs built and read here
  (plain objects plus OFS/REF deltas on the read side);
- **REST v3** (`/api/v3`) — repositories, refs, branches, commits,
  contents, labels, issues, comments, pull requests (three-way merge,
  squash), with GitHub-style pagination;
- **GraphQL** (`/api/graphql`) — the documents `gh` and
  `github-mcp-server` send, plus introspection, with opaque global ids
  and cursor pagination;
- **MCP** (`/mcp`) — JSON-RPC 2.0 Streamable HTTP, revision 2026-07-28
  (`server/discover`, legacy `initialize` too), with tools
  `create_repo`, `get_repo`, `create_issue`, `list_issues`,
  `create_pull_request`, `merge_pull_request` acting on the same store
  as REST.

## Running it

Local development (no env):

```sh
python3 main.py
# forge: listening on http://127.0.0.1:<port>
```

`PORT` may be set to pick a port; otherwise an ephemeral port is
chosen. Every endpoint needs a bearer token: when
`MAKEFUN_SHOP_TOKEN` is set in the process environment, only that
exact token authenticates; otherwise any non-empty bearer token does.

In the trial harness, `MAKEFUN_ENV_URL` is set: the forge binds an
ephemeral port (never 8080), POSTs `{"port": N}` to
`$MAKEFUN_ENV_URL/register`, then polls GET `$MAKEFUN_ENV_URL/done`
until `{"done": true}` and exits 0.

## Layout

- `main.py` — the whole forge: object model and packs, smart HTTP,
  REST, GraphQL, MCP, lifecycle.
- `.makefun/owner.json` — the owner's wallet address.

## Notes

- All timestamps the forge emits are fixed constants, so two runs on
  the same instance leave identical state.
- The viewer the bearer token names is `adaiversen` (id 1000): the
  suite's scenario is fixed by a public seed, so the token is opaque
  and the viewer is the scenario's viewer.
- The store is in-memory; restarting the process starts empty.
