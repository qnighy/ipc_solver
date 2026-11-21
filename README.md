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

## Usage (X Bot)

Requires Ruby 3.4 or later (for the `x` gem).

Create a developer app with the X account the bot runs as, and prepare its API
key, API key secret, access token, and access token secret (OAuth 1.0a, with
read and write permissions). Using the app owner's own access token lets the
mentions timeline be billed as Owned Reads.

```
$ make
$ cp x-config.toml.example x-config.toml
$ vim x-config.toml
$ bundle exec ruby x.rb
```

Instead of writing them in `x-config.toml`, each secret can be given via the
environment variables `X_API_KEY`, `X_API_KEY_SECRET`, `X_ACCESS_TOKEN`, and
`X_ACCESS_TOKEN_SECRET`. Each secret must be configured in exactly one place;
`x-config.toml` may be omitted entirely if all secrets come from the
environment.

The bot polls the mentions timeline every `bot.poll_interval` seconds
(default: 60) and replies to posts that begin with a mention of the bot.

Command line options:

- `-c`, `--config FILE`: config file (default: `./x-config.toml`, which may be
  absent)
- `--keep-scratch`: keep the per-request temporary directories for debugging
  (they contain post text)
- `--[no-]redact`: redact post text and solver output from logs (default:
  `log.redact` in the config file, or on)

The state (`x.sqlite3`) is stored in `$STATE_DIRECTORY` (as set by systemd's
`StateDirectory=`), or in the current directory if unset.

Data retention:

- Mentions older than `bot.max_age` (default: 1 hour) are ignored, including
  those that arrived while the bot was down.
- The text of a post is stored only until it is processed. Each request record
  (post ID and state) is deleted `bot.retention` (default: 2 hours) after the
  post was created.
- Usernames are neither fetched nor stored; replies are threaded by post ID.
- A request interrupted while being processed (e.g. by a crash) is not retried,
  to avoid replying twice.

Logs are written to stderr. Set `LOG_LEVEL` (e.g. `debug`, `info`, `warn`) to
change the verbosity (default: `info`). Unless redaction is disabled, logs
contain post and user IDs but no post text, solver output, or usernames.

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

The bot listens to the streaming API (`/api/v1/streaming/user/notification`)
and additionally polls notifications every 3 minutes. If the streaming
connection drops or stays silent for 60 seconds (Mastodon sends a heartbeat
every 15 seconds), it reconnects with exponential backoff (up to 5 minutes) and
re-checks notifications missed in between. Failed API calls (e.g. while the
server is restarting) are logged and retried rather than terminating the bot.

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


