package utils;

import java.util.List;
import java.util.Set;

import models.Language;
import controllers.Application;
import play.i18n.Lang;
import play.i18n.Messages;

/**
 * This class overwrites the Messages class built into play so we can
 * overwrite the default language with the language that was set by the
 * current logged in user.
 */
public class LangMessages extends Messages {
    public static String get(String s, Object... objects) {
        try {
            if (Application.isLanguageSet()) {
                return Messages.get(Lang.forCode(Application.getLanguage().getOfficialCode()), s, objects);
            }
        } catch (Exception e) {
            // Do nothing
        }

        return Messages.get(s, objects);
    }
    
    public static Language getLanguage(Set<Language> languages) {
    	Language preference = Application.getLanguage();

    	if(languages.contains(preference)) {
    		return preference;
    	} else {
    		for(Language l : Language.values()) {
    			if(languages.contains(l)) {
    				return l;
    			}
    		}
    	}
    	return null;
    }
}
