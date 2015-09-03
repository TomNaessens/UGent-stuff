package models;

import java.util.ArrayList;
import java.util.List;

import utils.LangMessages;

public enum FileType {
    CSV,
    XLS,
    XLSX;

    public static List<String> list() {
        FileType[] ds = values();
        List<String> res = new ArrayList<String>(ds.length);

        for (FileType d : ds)
            res.add(d.toString());

        return res;
    }

    @Override
    public String toString(){
       if (name().equals("XLS")||name().equals("XLSX")) {
          return "excel (" + name().toLowerCase()+")" ;
       } else {
          return name().substring(0,1).toUpperCase() + name().substring(1,name().length()).toLowerCase();
       }
    }

}
