# IPC solver

## Description

It determines whether a given statement in Intuitionistic
Propositional Calculus (IPC) is provable or not.

## Dependencies

- OCaml
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


