package models;

import java.util.ArrayList;
import java.util.List;

import utils.LangMessages;

public enum Difficulties {
    EASY,
    AVERAGE,
    HARD;

    public static List<String> list() {
        Difficulties[] ds = values();
        List<String> res = new ArrayList<String>(ds.length);

        for (Difficulties d : ds)
            res.add(d.toString());

        return res;
    }
    
    public String toString(){
    	return LangMessages.get("enum.difficulties."+name());
    }
}
