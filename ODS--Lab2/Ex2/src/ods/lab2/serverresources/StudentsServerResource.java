package ods.lab2.serverresources;

import java.util.List;

import ods.lab2.entities.Student;
import ods.lab2.resources.StudentResource;
import ods.lab2.services.StudentService;

import org.restlet.data.Form;
import org.restlet.representation.Representation;
import org.restlet.resource.Delete;
import org.restlet.resource.Get;
import org.restlet.resource.Post;
import org.restlet.resource.Put;
import org.restlet.resource.ServerResource;

public class StudentsServerResource extends ServerResource implements StudentResource {

	/**
	 * There's no need to create an extra class, we can use the Service uses in
	 * StudentServerResource again; hooray for modularity!
	 */

	StudentService studentService;

	public StudentsServerResource() {
		super();

		this.studentService = new StudentService();
	}

	@Get
	public String retrieve() {
		Form form = getRequest().getResourceRef().getQueryAsForm();

		try {
			if (form.getValuesMap().get("id") != null) {
				// Retrieval based on groupnumber
				List<Student> students = studentService.getGroupOfStudentsByID(Integer.parseInt(form.getValuesMap()
						.get("id")));

				if (!students.isEmpty()) {
					return students.toString();
				} else {
					return "No students found.";
				}

			} else {

				// No information provided: return all students
				List<Student> students = studentService.getAllStudents();

				if (!students.isEmpty()) {
					return students.toString();
				} else {
					return "No students found.";
				}
			}

		} catch (NumberFormatException e) {
			return "Please make sure your id is a valid number";
		}

	}

	@Post
	public String store(Representation entity) {
		return "No multiple store has to be implemented";

	}

	@Put
	public String update(Representation entity) {
		return "No multiple store has to be implemented";
	}

	@Delete
	public String remove() {
		Form form = getRequest().getResourceRef().getQueryAsForm();

		if (form.getValuesMap().containsKey("id")) {

			String idstring = form.getValuesMap().get("id");

			// If the id contains a comma, we know we want to delete a list of
			// ids. Otherwise, we want to delete a group
			if (idstring.contains(",")) {
				String[] ids = idstring.split(",");

				String result = "";

				for (String id : ids) {
					try {
						long longId = Long.parseLong(id);

						if (studentService.getStudentById(longId) != null) {
							studentService.removeStudentByID(longId);

							result += "The student with id " + longId + " has succesfully been deleted.\n";
						} else {
							result += "The student with id " + id + " could not be found.\n";
						}

					} catch (NumberFormatException ex) {
						result += "The id " + id + " could not be interpreted.\n";
					}
				}

				return result;

			} else {

				int id;

				try {
					id = Integer.parseInt(form.getValuesMap().get("id"));
				} catch (NumberFormatException ex) {
					return "Please make sure your id is a number";
				}

				studentService.removeGroup(id);

				return "Group succesfully removed";
			}
		}

		return "Please specify a group number of multiple IDs";
	}
}
