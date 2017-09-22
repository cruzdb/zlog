#!/bin/sh
set -e

# adapted from github.com/ceph/ceph make-dist script

if [ ! -d .git ]; then
  echo "no .git directory found."
  exit 1
fi

# get version
version=$1
[ -z "$version" ] && version=`git describe --match 'v*' | sed 's/^v//'`
echo "version $version"

# clean out old cruft...
outfile="zlog-$version"
echo "cleanup..."
rm -f $outfile*

# update submodules
echo "updating submodules..."
force=$(if git submodule usage 2>&1 | grep --quiet 'update.*--force'; then echo --force ; fi)
if ! git submodule sync || ! git submodule update $force --init --recursive; then
  echo "Error: could not initialize submodule projects"
  echo "  Network connectivity might be required."
  exit 1
fi

# build tarball
echo "building tarball..."
bin/git-archive-all.sh --prefix ${outfile}/ --verbose ${outfile}.tar

# populate files with version strings
(git rev-parse HEAD ; git describe) 2> /dev/null > src/.git_version

ln -s . ${outfile}
tar cvf ${outfile}.version.tar ${outfile}/src/.git_version
tar --concatenate -f ${outfile}.both.tar ${outfile}.version.tar
tar --concatenate -f ${outfile}.both.tar ${outfile}.tar
mv ${outfile}.both.tar ${outfile}.tar
rm -f ${outfile} ${outfile}.version.tar

echo "compressing..."
bzip2 -9 ${outfile}.tar

echo "done."
