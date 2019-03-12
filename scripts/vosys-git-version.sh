#! /bin/sh

TARGET=$1

if [ -z "$TARGET" ]; then
	echo "Please pass a target filename in parameter"
	exit 1
fi

GIT_DIR=$SRC_PATH/.git
GIT_BASE=$GIT_DIR
if [[ -f "$GIT_DIR" ]]; then
	GIT_DIR=$(cat $GIT_DIR | cut -d" " -f2)
	GIT_BASE=$GIT_DIR/../../
fi

if [ -d $GIT_DIR ]; then
    REF=$(cat $GIT_DIR/HEAD | cut -b6-)
    BRANCH=$(echo $REF | cut -b12-)
    COMMIT=$(cat $GIT_BASE/$REF | cut -b-8)

    echo "  Updating git commit information ..." >&2

    text="#define VOSYS_GIT_COMMIT \"$BRANCH/$COMMIT\""
else
    echo "  Could not find git directory. Assuming not under version control."
    text="#define VOSYS_GIT_COMMIT \"<not under version control>\""
fi

echo "$text" > $TARGET
