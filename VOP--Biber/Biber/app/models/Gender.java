package models;

import utils.LangMessages;

public enum Gender {
	MALE,
	FEMALE;
	
	public static Gender getGender(String s){
		if(s.equalsIgnoreCase(LangMessages.get("enum.gender.MALE"))
				|| s.equalsIgnoreCase(LangMessages.get("enum.gender.MALE.ab")))
		{
			return MALE;
		}
		
		if(s.equalsIgnoreCase(LangMessages.get("enum.gender.FEMALE"))
				|| s.equalsIgnoreCase(LangMessages.get("enum.gender.FEMALE.ab")))
		{
			return FEMALE;
		}
		return null;
		
		
	}

    /**
     * Custom toString method
     * @return the name of the value, with the first letter capitalized, and the rest of the word lowercase.
     */
    @Override
    public String toString(){
        return LangMessages.get("enum.gender."+name()).substring(0,1).toUpperCase() + LangMessages.get("enum.gender."+name()).substring(1,LangMessages.get("enum.gender."+name()).length()).toLowerCase();
    }
}
