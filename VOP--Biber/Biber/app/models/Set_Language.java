package models;

import javax.persistence.Entity;
import javax.persistence.Id;

import play.db.ebean.Model;

@Entity
public class Set_Language extends Model {
	
	@Id
	public Long id;

    public Language language;
    public String title;

    public Set_Language(String title, Language language) {
        this.language = language;
        this.title = title;
    }
}
