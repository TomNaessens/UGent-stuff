package models;

import utils.LangMessages;

import java.util.ArrayList;
import java.util.List;

public enum Level {
	
	EWOK("10-12"),
	WOOKIE("12-14"),
	PADAWAN("14-16"),
	JEDI("16-18");
	
	/**
	 * a String representation of the age group corresponding with the level
	 */
	private String ageGroup;
	public String ageGroup(){
		return ageGroup;
	}

    /**
     * Method to give all levels in a list, used by composeSet view.
     * @return
     */
    public static List<String> getAll(){
        List<String> list = new ArrayList<String>();
        for(Level l : Level.values()) {
        	list.add(l.toString()+" ("+l.ageGroup()+")");
        }
        return list;
    }
	
	Level(String ageGroup){
		this.ageGroup = ageGroup;
	}
	
	/**
	 * returns the level corresponding with the String representation of the level
	 * @param String representation of level
	 * @return enum level
	 */
	public static Level getLevel(String level) {
		return valueOf(level.toUpperCase());
	}
	
	public String toString(){
		return LangMessages.get("enum.level." + name());
	}
	
	
	

}
