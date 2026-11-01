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


