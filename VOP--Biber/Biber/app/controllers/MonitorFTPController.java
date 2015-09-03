package controllers;


import controllers.security.SecuredAdmin;
import models.FileServer;
import models.FileServerStatus;
import org.apache.commons.net.ftp.FTPClient;
import org.codehaus.jackson.node.JsonNodeFactory;
import org.codehaus.jackson.node.ObjectNode;
import play.api.mvc.Call;
import play.data.Form;
import play.libs.Json;
import play.mvc.Controller;
import play.mvc.Result;
import play.mvc.Security;
import utils.LangMessages;
import utils.Obfuscate;
import views.html.admin.ftp.addServer;
import views.html.admin.ftp.serverOverview;

import javax.persistence.PersistenceException;
import java.io.IOException;
import java.net.SocketException;
import java.util.List;


@Security.Authenticated(SecuredAdmin.class)
public class MonitorFTPController extends Controller {

    public static Result renderOverview() {

        List<FileServer> servers = FileServer.all();

        for(FileServer server : servers) {
            server.pass = Obfuscate.deObfuscate(server.pass);
        }

        return ok(serverOverview.render(servers));
    }

    public static Result renderAddServer() {
        Call call = new Call("POST", routes.MonitorFTPController.addServer().url());
        return ok(addServer.render(Form.form(FileServer.class), call));
    }

    public static Result getStatus() {
        ObjectNode result = Json.newObject();

        List<FileServer> servers = FileServer.all();

        for (FileServer server : servers) {
            ObjectNode serverNode = JsonNodeFactory.instance.objectNode();

            try {
                FTPClient client = new FTPClient();
                client.connect(server.host);
                boolean loggedIn = client.login(server.username, Obfuscate.deObfuscate(server.pass));

                if(!loggedIn) throw new Exception();

                client.logout();
                client.disconnect();

                serverNode.put("serverStatus", FileServerStatus.ONLINE.toString());

            } catch (Exception e) {
                serverNode.put("serverStatus", FileServerStatus.OFFLINE.toString());
            }


            result.put(Long.toString(server.id), serverNode);
        }

        return ok(result);
    }

    public static Result addServer() {
        Form<FileServer> addServerForm = Form.form(FileServer.class).bindFromRequest();

        if (addServerForm.hasErrors()) {
            Call call = new Call("POST", routes.MonitorFTPController.addServer().url());
            return badRequest(addServer.render(addServerForm, call));

        } else {

            FileServer f = addServerForm.get();
            f.pass = Obfuscate.obfuscate(f.pass);
            f.save();

            return redirect(routes.MonitorFTPController.renderOverview());
        }
    }

    public static Result renderEditServer(Long id) {
        Call call = new Call("POST", routes.MonitorFTPController.editServer(id).url());

        FileServer f = FileServer.find.byId(id);

        f.pass = Obfuscate.deObfuscate(f.pass);

        return ok(addServer.render(Form.form(FileServer.class).fill(f), call));
    }

    public static Result editServer(Long id) {
        Form<FileServer> addServerForm = Form.form(FileServer.class).bindFromRequest();

        if (addServerForm.hasErrors()) {
            Call call = new Call("POST", routes.MonitorFTPController.addServer().url());
            return badRequest(addServer.render(addServerForm, call));

        } else {
            FileServer f = FileServer.find.byId(id);

            f.host = addServerForm.get().host;
            f.port = addServerForm.get().port;
            f.publicLink = addServerForm.get().publicLink;
            f.questionFolder = addServerForm.get().questionFolder;
            f.username = addServerForm.get().username;
            f.pass = Obfuscate.obfuscate(addServerForm.get().pass);

            f.save();

            return redirect(routes.MonitorFTPController.renderOverview());
        }
    }

    public static Result removeServer(Long id) {
        try {
            FileServer.find.byId(id).delete();
            return redirect(routes.MonitorFTPController.renderOverview());
        } catch (PersistenceException e) {
            flash("important", LangMessages.get("MonitorFTP.errors.cantDeleteServer"));
            return redirect(routes.MonitorFTPController.renderOverview());
        }
    }

}