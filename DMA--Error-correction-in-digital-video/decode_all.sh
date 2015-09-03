for i in 0 1 2 3 4 5
do
  for method in "simple" "complex"
  do
    if [[ ("$i" == 4 || "$i" == 0) && "$method" == "complex" ]]
    then
      break
    fi

    for fragment in "group" "synthetic" "natural"
    do
      FILE="Meetresultaten/Time/"$fragment"_"$method"_"$i".txt"
      echo $FILE
      rm $FILE 2> /dev/null
      touch $FILE
      ./$fragment"_"$method".sh" $i | grep "Time elapsed" > $FILE
    done
  done
done
