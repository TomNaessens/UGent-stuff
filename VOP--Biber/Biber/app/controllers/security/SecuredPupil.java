package controllers.security;

import controllers.routes;
import play.*;
import play.mvc.*;
import play.mvc.Http.*;

import models.*;
import utils.LangMessages;

/*
 *  If this getUsername() returns a value, then the authenticator considers the user to be logged in as pupil, 
 *  and lets the request proceed. If however the method returns null, then the authenticator will 
 *  block the request, and instead invoke onUnathorized
 */

public class SecuredPupil extends Security.Authenticator{
    
    /*
     * (non-Javadoc)
     * @see play.mvc.Security.Authenticator#getUsername(play.mvc.Http.Context)
     * Only return value if user role is pupil
     */
    @Override
    public String getUsername(Context ctx) {
        if(ctx.session().get("role") == null)
            return null;
        if(ctx.session().get("role").equals("pupil") || ctx.session().get("role").equals("admin") || ctx.session().get("role").equals("organizer") || ctx.session().get("role").equals("teacher"))
            return ctx.session().get("bebrasId");
        return null;
    }

    /*
     * (non-Javadoc)
     * @see play.mvc.Security.Authenticator#onUnauthorized(play.mvc.Http.Context)
     * TODO: For example if teacher tries to register organizer -> not redirecting to login, but error message!!!!
     */
    @Override
    public Result onUnauthorized(Context ctx) {
        ctx.flash().put("returnUrl_invisible", ctx.request().uri());
        ctx.flash().put("error", LangMessages.get("notAuthorized.pupil", ctx.request().uri()));
        return redirect(routes.Application.login());
    }

}
