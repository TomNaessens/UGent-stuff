package utils;

import org.apache.commons.mail.*;
import play.Play;

import java.io.File;

public class Mail {

    public static void sendMailWithAttachment(String emailAddress,
                                              String subject, String message, File fileToAttach) throws EmailException {
        if(Play.isTest()) return;
        EmailAttachment attachment = new EmailAttachment();
        attachment.setPath(fileToAttach.getAbsolutePath());
        attachment.setDisposition(EmailAttachment.ATTACHMENT);
        attachment.setName(fileToAttach.getName());

        // Create the email message
        MultiPartEmail email = new MultiPartEmail();
        configureEmail(email);
        email.addTo(emailAddress);
        email.setFrom("biber@biber.ugent.be");
        email.setSubject(subject);
        email.setMsg(message);

        // add the attachment
        email.attach(attachment);

        // send the email
        email.send();
    }

    public static void sendMail(String emailAddress, String subject,
                                String message) throws EmailException {
        if(Play.isTest()) return;
        Email email = new SimpleEmail();
        configureEmail(email);
        email.setFrom("biber@biber.ugent.be");
        email.setSubject(subject);
        email.setMsg(message);
        email.addTo(emailAddress);
        email.send();
    }

    private static void configureEmail(Email email) {
        if (Play.isProd()) {
            email.setHostName("smtp.ugent.be");
        }
        else if(Play.isTest()){
            return;
        }
        else {
            email.setHostName("smtp.gmail.com");
            email.setSmtpPort(465);
            email.setSSL(true);
            email.setAuthenticator(new DefaultAuthenticator("hannes.biberteam@gmail.com", "biber123"));
        }
    }

}
