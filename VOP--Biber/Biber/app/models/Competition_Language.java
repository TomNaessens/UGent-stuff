package models;

import play.db.ebean.Model;

import javax.persistence.Entity;
import javax.persistence.Id;

@Entity
public class Competition_Language extends Model {
    // TODO: figure out if we can remove the id, since this is a relation, not an entity...
    @Id
    public Long id;

    public Language language;
    public String title;

    public Competition_Language(String title, Language language) {
        this.language = language;
        this.title = title;
    }
}
