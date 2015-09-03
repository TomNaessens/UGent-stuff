for i in 0 1 2 3 4 5
do
  for method in "simple" "complex"
  do
    if [[ ("$i" == 0 || "$i" == 2 || "$i" == 4) && "$method" == "complex" ]]
    then
      break
    fi

    for fragment in "group" "common_synthetic" "common_natural"
    do

      if [[ "$fragment" == "group" || "$fragment" == "common_natural" ]]
      then
        width=640
        height=272
      else
        width=816
        height=576
      fi

      FILE="Meetresultaten/PSNR/"$fragment"_"$method"_"$i".txt"
      echo $FILE
      rm $FILE 2> /dev/null
      touch $FILE
      ../PSNR_Tool.exe Video/$fragment"_40.yuv" Video/$fragment"_40_"$method"_"$i.yuv $width $height >> $FILE
    done
  done
done
