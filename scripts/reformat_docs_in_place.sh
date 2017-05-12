tmpfile=$(mktemp /tmp/tmp_conversion.XXXXXX)
python convert.py $1 > $tmpfile && mv $tmpfile $1
