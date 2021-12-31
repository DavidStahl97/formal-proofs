find . -name '*.agda' | while read file
do
  echo "check file $file"
  agda $file
  echo "check file $file succesful"
done