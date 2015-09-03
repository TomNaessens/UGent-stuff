package ods.lab2.serverresources;

import ods.lab2.entities.Quotation;
import ods.lab2.resources.QuotationResource;
import ods.lab2.services.QuotationService;

import org.restlet.data.Form;
import org.restlet.resource.Delete;
import org.restlet.resource.Get;
import org.restlet.resource.Post;
import org.restlet.resource.Put;
import org.restlet.resource.ResourceException;
import org.restlet.resource.ServerResource;
import org.restlet.representation.Representation;

public class QuotationServerResource extends ServerResource implements
		QuotationResource {
	
	private QuotationService quotationService;
	
	public QuotationServerResource() {
		super();
		
		quotationService = new QuotationService();
	}
	
	protected void doInit() throws ResourceException {
		super.doInit();
	}

	@Get
	public String retrieve() {

		Form form = getRequest().getResourceRef().getQueryAsForm();
		String id = form.getValuesMap().get("id");

		Quotation quotation = quotationService.getQuotationById(Long
				.parseLong(id));

		return quotation.toString();
	}

	@Post
	public String store(Representation entity) {
		return "Doesn't have to be implemented!";
	}

	@Put
	public String update(Representation entity) {
		return "Doesn't have to be implemented!";
	}

	@Delete
	public String remove() {
		return "Doesn't have to be implemented!";
	}
}
