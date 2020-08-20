# By default, just create a new minor version. If we ever need to change
# major/patch version just do it manually.
read -r version_line
major=$(echo $version_line | cut -d . -f 1)
minor=$(echo $version_line | cut -d . -f 2)
patch=$(echo $version_line | cut -d . -f 3)
echo "$major.$(expr $minor + 1).0"
