package models;

import java.net.MalformedURLException;
import java.net.URL;
import java.util.UUID;

import javax.persistence.Entity;
import javax.persistence.Id;

import org.apache.commons.mail.EmailException;
import org.joda.time.DateTime;

import controllers.routes;

import play.Play;
import play.api.mvc.Call;
import play.data.validation.Constraints;
import play.db.ebean.Model;
import play.data.format.Formats;
import play.i18n.Messages;
import play.mvc.Http.Context;
import utils.Mail;

@Entity
public class Token extends Model{

    private static final int EXPIRATION_DAYS = 1;
    
    @Id
    public String token;
    
    @Constraints.Required
    @Formats.NonEmpty
    public String bebrasId;
    
    public DateTime dateOfCreation;
    
    @Constraints.Required
    @Formats.NonEmpty
    public String email;
    
    public static Model.Finder<String, Token> find = new Finder(String.class, Token.class);
    
    /**
     *  Retrieves a token from the DB with given token string.
     * @param token
     * @return a Token
     */
    public static Token findByToken(String token) {
        return find.where().eq("token", token).findUnique();
    }
    
    
    /**
     * @return true if the reset token is too old to use, false otherwise.
     */
    public boolean isExpired() {
        return dateOfCreation != null && dateOfCreation.plusDays(EXPIRATION_DAYS).isBeforeNow();
    }
    
    /**
     * Return a new Token.
     *
     * @param user  user
     * @param email email for a token change email
     * @return a reset token
     */
    public static Token createNewToken(Person person, String email) {
        for(Token t : Token.find.where().eq("bebrasId", person.bebrasId).findList())
            t.delete(); //delete all previous tokens of user
        Token token = new Token();
        token.dateOfCreation = DateTime.now();
        token.token = UUID.randomUUID().toString();
        token.bebrasId = person.bebrasId;
        token.email = email;
        token.save();
        return token;
    }
    
    /**
     * Send the Email to confirm ask new password.
     *
     * @param user the current user
     * @throws EmailException 
     * @throws java.net.MalformedURLException if token is wrong.
     */
    public static void sendMailContainingToken(Person person) throws EmailException {
        Token token = createNewToken(person, null);
        Call callUrl = routes.Reset.renderResetPassword(token.token);
        try {
            URL url=null;
            if (Play.isDev() || Play.isTest()) {
                url = new URL(callUrl.absoluteURL(Context.current().request()));
            }
            if (Play.isProd()) {
                String urlString = "http://biber.ugent.be/play/resetPassword/" + token.token;
                url = new URL(urlString);
            }
            Mail.sendMail(
                    person.email,
                    utils.LangMessages.get("resetPassword.mail.subject"),
                    utils.LangMessages.get("resetPassword.mail.message",
                            url.toString()));
        } catch (MalformedURLException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        } // validate the URL
    }
    
    
}
