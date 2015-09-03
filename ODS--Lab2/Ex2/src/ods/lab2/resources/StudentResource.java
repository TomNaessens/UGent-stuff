package ods.lab2.resources;

import org.restlet.representation.Representation;
import org.restlet.resource.Delete;
import org.restlet.resource.Get;
import org.restlet.resource.Post;
import org.restlet.resource.Put;

public interface StudentResource {
	@Get
	public String retrieve();

	@Post
	public String store(Representation entity);

	@Put
	public String update(Representation entity);

	@Delete
	public String remove();
}
