package ods.lab2.application;

import ods.lab2.serverresources.QuotationServerResource;
import ods.lab2.serverresources.StudentServerResource;
import ods.lab2.serverresources.StudentsServerResource;

import org.restlet.Application;
import org.restlet.Restlet;
import org.restlet.resource.Directory;
import org.restlet.routing.Router;


public class LabApplication extends Application {
	
	@Override
	public synchronized Restlet createInboundRoot() {
		// Create a router Restlet that routes each call to a
		// new instance of HelloWorldResource.
		Router router = new Router(getContext());
		router.attachDefault(new Directory(getContext(), "war:///"));
		router.attach("/quotation", QuotationServerResource.class);
		router.attach("/student", StudentServerResource.class);
		router.attach("/students", StudentsServerResource.class);
		return router;
	}
}
