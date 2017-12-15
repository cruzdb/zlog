# Contributing to ZLog / CruzDB

## Getting Started

We want the process of becoming a new contributor to be as easy as possible ([idea for improvement?](https://github.com/cruzdb/zlog/issues/new?title=suggestion+for+improving+project+for+new+contributors)). We've put together the following list of tasks that have low complexity and are beginner-friendly.

* Work on an [easy](https://github.com/cruzdb/zlog/issues?q=is%3Aissue+is%3Aopen+label%3AE-easy) or [intermediate](https://github.com/cruzdb/zlog/issues?q=is%3Aissue+is%3Aopen+label%3AE-intermediate) issue
* Fix a [Coverity defect](#coverity-scan) warning

Finding something to work on is only part of the process. We encourage anyone interested in becoming involved as a contributor to reach out to a developer for help or mentoring.

## Commit Messages

Please sign-off your commits by appending the following to your commit message:

`Signed-off-by: Joe Smith <joe.smith@email.com>`

If you set your `user.name` and `user.email` in git config (e.g. $HOME/.gitconfig), then you can sign your commit automatically with `git commit -s` (e.g. `git commit -s -m "subsystem: new feature"`).

## Coverity Scan

We run [Coverity static analysis](https://scan.coverity.com/projects/cruzdb-zlog) periodically on the `covery_scan` branch. The list of [defects can be found here](https://scan.coverity.com/projects/cruzdb-zlog), but you'll need to be added to the project to view the defects. On the defects page click the *Add me to project* link and we'll grant you access. When submitting a patch that fixes a Coverity issue, use a commit message of the form `coverity/<id>: <description>` where `<id>` is the Coverity ID (CID).
