# IPC solver

## Description

It determines whether a given statement in Intuitionistic
Propositional Calculus (IPC) is provable or not.

## Dependencies

- OCaml
- MiniSat executable (for refutation by Kripke models)
- LaTeX (for drawing proof diagrams)

## Usage (Command Line)

```
$ make
$ ./ipc_solver <<< "~~(A \/ ~A)"
$ ./ipc_solver <<< "A \/ ~A"
```

## Usage (LaTeX)

```
$ make
$ ./ipc_solver --latex ipc.tex <<< "~~(A \/ ~A)"
$ latex ipc.tex
$ dvipdfmx ipc.dvi
```

## Usage (Twitter Bot)

Please prepare your consumer key, consumer secret, access token, and access token secret.

```
$ make
$ cp twitter-config.rb.example twitter-config.rb
$ vim twitter-config.rb
$ bundle exec ruby twitter.rb
```

Instead of writing them in `twitter-config.rb`, each secret can be given via
the environment variables `TWITTER_CONSUMER_KEY`, `TWITTER_CONSUMER_SECRET`,
`TWITTER_ACCESS_TOKEN`, and `TWITTER_ACCESS_TOKEN_SECRET`. Each secret must be
configured in exactly one place; `twitter-config.rb` may be omitted entirely
if all secrets come from the environment.

Command line options:

- `-c`, `--config FILE`: config file (default: `./twitter-config.rb`, which
  may be absent)
- `--keep-scratch`: keep the per-request temporary directories for debugging

The state (`twitter-db`, `twitter-log.txt`) is stored in `$STATE_DIRECTORY`
(as set by systemd's `StateDirectory=`), or in the current directory if unset.

Logs are written to stderr; warnings and errors are also appended to
`twitter-log.txt`. Set `LOG_LEVEL` (e.g. `debug`, `info`, `warn`) to change
the verbosity (default: `info`).

## Usage (Mastodon Bot)

Please prepare an access token with the permissions listed in `mastodon-config.toml.example`.

```
$ make
$ cp mastodon-config.toml.example mastodon-config.toml
$ vim mastodon-config.toml
$ bundle exec ruby mastodon.rb
```

Secrets can be given via the environment variables `MASTODON_ACCESS_TOKEN`,
`MASTODON_CLIENT_KEY`, and `MASTODON_CLIENT_SECRET` instead of
`mastodon-config.toml`. Each secret must be configured in at most one place
(`access_token` is required; `client_key` and `client_secret` are optional).
Non-secret settings such as `domain` are read from `mastodon-config.toml` only.

Command line options:

- `-c`, `--config FILE`: config file (default: `./mastodon-config.toml`)
- `--keep-scratch`: keep the per-request temporary directories for debugging

The state (`mastodon.sqlite3`) is stored in `$STATE_DIRECTORY` (as set by
systemd's `StateDirectory=`), or in the current directory if unset. Each
request is processed in a fresh temporary directory (under `$TMPDIR`, default
`/tmp`), which is removed afterwards unless `--keep-scratch` is given.

Logs are written to stderr. Set `LOG_LEVEL` (e.g. `debug`, `info`, `warn`) to
change the verbosity (default: `info`). When a request fails ("An error
occured"), the log includes the input, the exit status, and the tail of the
solver/LaTeX output.

The `ipc_solver` binary and the `*-make-image.sh` scripts are always looked up
next to the Ruby script, so the bot can be started from any directory and the
source tree itself may be read-only (e.g. in the Nix store). For example, as a
systemd service:

```ini
[Service]
StateDirectory=ipc-solver
PrivateTmp=yes
ExecStart=/path/to/ruby /path/to/ipc_solver/mastodon.rb --config /etc/ipc-solver/mastodon-config.toml
```


