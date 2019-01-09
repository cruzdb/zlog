#!/bin/sh
set -e

# adapted from github.com/ceph/ceph make-dist script

if [ ! -d .git ]; then
  echo "no .git directory found."
  exit 1
fi

# get version from git tags and the current working directory version. it will
# show vX.Y.Z-patch_count-sha1 where X.Y.Z is the most recent reachable tag. And
# run on a checked out version that matches a tag the version will be exactly:
# x.y.z for a clean release name.
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

# if the version has '-' in it, it has a 'release' part,
# like vX.Y.Z-N-g<shortsha1>.  If it doesn't, it's just
# vX.Y.Z.  Handle both, and translate - to . for rpm
# naming rules (the - separates version and release).

if expr index ${version} '-' > /dev/null; then
	rpm_version=`echo ${version} | cut -d - -f 1-1`
	rpm_release=`echo ${version} | cut -d - -f 2- | sed 's/-/./'`
else
	rpm_version=${version}
	rpm_release=0
fi

for tmpl in zlog.spec.in alpine/APKBUILD.in; do
  cat ${tmpl} |
    sed "s/@VERSION@/${rpm_version}/g" |
    sed "s/@RELEASE@/${rpm_release}/g" |
    sed "s/@TARBALL_BASENAME@/${outfile}/g" > `echo ${tmpl} | sed 's/.in$//'`
done

ln -s . ${outfile}
tar cvf ${outfile}.version.tar ${outfile}/src/.git_version ${outfile}/alpine/APKBUILD
tar --concatenate -f ${outfile}.both.tar ${outfile}.version.tar
tar --concatenate -f ${outfile}.both.tar ${outfile}.tar
mv ${outfile}.both.tar ${outfile}.tar
rm -f ${outfile} ${outfile}.version.tar

echo "compressing..."
bzip2 -9 ${outfile}.tar

echo "done."
