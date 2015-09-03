package ods.lab2.serverresources;

import java.io.IOException;

import ods.lab2.entities.Student;
import ods.lab2.resources.StudentResource;
import ods.lab2.services.StudentService;

import org.json.JSONException;
import org.json.JSONObject;
import org.restlet.data.Form;
import org.restlet.ext.json.JsonRepresentation;
import org.restlet.resource.Delete;
import org.restlet.resource.Get;
import org.restlet.resource.Post;
import org.restlet.resource.Put;
import org.restlet.resource.ResourceException;
import org.restlet.resource.ServerResource;
import org.restlet.representation.Representation;

public class StudentServerResource extends ServerResource implements StudentResource {

	StudentService studentService;

	public StudentServerResource() {
		super();

		studentService = new StudentService();
	}

	protected void doInit() throws ResourceException {
		super.doInit();
	}

	@Get
	public String retrieve() {
		Form form = getRequest().getResourceRef().getQueryAsForm();

		try {
			if (form.getValuesMap().containsKey("id")) {

				// Retrieval based on primary key
				Student student = studentService.getStudentById(Long.parseLong(form.getValuesMap().get("id")));
				return (student != null) ? student.toString() : "Student not found.";

			} else if (form.getValuesMap().containsKey("name") && form.getValuesMap().containsKey("surname")) {

				// Retrieval based on name and surname
				Student student = studentService.getStudentByName(form.getValuesMap().get("name"), form.getValuesMap()
						.get("surname"));

				return (student != null) ? student.toString() : "Student not found.";

			} else {
				return "Please provide an ID or a name and a surname.";
			}

		} catch (NumberFormatException e) {
			return "Please make sure your id is a valid number";
		}
	}

	@Post
	public String store(Representation entity) {

		if (entity == null) {
			return "Please provide the needed information in the json payload.";
		}

		try {
			JSONObject jsonRequest = (new JsonRepresentation(entity)).getJsonObject();

			if (!jsonRequest.has("name") || !jsonRequest.has("surname")) {
				return "Please define a name and a surname";
			}

			String name = jsonRequest.getString("name");
			String surname = jsonRequest.getString("surname");

			if (studentService.getStudentByName(name, surname) == null) {

				studentService.addStudent(name, surname,
						jsonRequest.has("groupnumber") ? jsonRequest.getString("groupnumber") : null,
						jsonRequest.has("checksum") ? jsonRequest.getString("checksum") : null);

				return "Student " + name + " " + surname + " has been added!";
				
			} else {
				return "Student already exists";
			}

		} catch (NumberFormatException e) {
			return "Error: groupid or checksum cannot be casted to integers.";
		} catch (IOException e) {
			return "An IOError occured.";
		} catch (JSONException e) {
			return "A JSONException occured.";
		}
	}

	@Put
	public String update(Representation entity) {
		if (entity == null) {
			return "Please provide the needed information in the json payload.";
		}

		try {
			JSONObject jsonRequest = (new JsonRepresentation(entity)).getJsonObject();

			Long id;

			if (jsonRequest.has("id")) {
				id = Long.parseLong(jsonRequest.getString("id"));
			} else {
				return "Please define an ID to edit!";
			}

			/*
			 * This is quite an extensive check: We pull the current student
			 * from the database and check if the student exists. If this is the
			 * case, we do another check to make sure that the new values do not
			 * match the values of another student in the database to avoid
			 * duplication.
			 */
			Student student = studentService.getStudentById(id);

			if (student != null) {
				String name = (jsonRequest.has("name")) ? jsonRequest.getString("name") : student.getName();
				String surname = (jsonRequest.has("surname")) ? jsonRequest.getString("surname") : student.getSurname();
				Integer groupnumber = (jsonRequest.has("groupnumber")) ? Integer.parseInt(jsonRequest
						.getString("groupnumber")) : student.getGroupnumber();
				Integer checksum = (jsonRequest.has("checksum")) ? Integer.parseInt(jsonRequest.getString("checksum"))
						: student.getChecksum();

				Student foundStudent = studentService.getStudentByName(name, surname);
				if (foundStudent == null) {
					// The resulting student does not exist; update him!
					studentService.editStudent(name, surname, groupnumber, checksum, student);
					return "Student succesfully updated!";
				} else {
					// The resulting student does exist! Maybe he just updated
					// his groupnumber or checksum?
					if (foundStudent.getID() == student.getID()
							&& (groupnumber != foundStudent.getGroupnumber() || checksum != foundStudent.getChecksum())) {
						// It is the same user and or his groupnumber or his
						// checksum are different: Update him!
						studentService.editStudent(name, surname, groupnumber, checksum, student);
						return "Student succesfully updated!";
					} else {
						// Different ID's or nothing is updated? Abort!
						return "A student with this name and information already exists.";
					}
				}

			} else {
				return "The student with id " + id + " has not been found!";
			}

		} catch (NumberFormatException e) {
			return "Error: groupid or checksum cannot be casted to integers.";
		} catch (IOException e) {
			return "An IOError occured.";
		} catch (JSONException e) {
			return "A JSONException occured.";
		}

	}

	@Delete
	public String remove() {
		Form form = getRequest().getResourceRef().getQueryAsForm();

		// Input validation
		if (form.getValuesMap().get("name") == null || form.getValuesMap().get("surname") == null
				|| form.getValuesMap().get("checksum") == null) {
			return "Please use the following parameters:" + "/student?name=student_name" + "&surname=student_surname"
					+ "&checksum=checksum";
		}

		// The variables exist, hooray!
		String name = form.getValuesMap().get("name");
		String surname = form.getValuesMap().get("surname");
		int checksum = 0;
		try {
			checksum = Integer.parseInt(form.getValuesMap().get("checksum"));
		} catch (NumberFormatException ex) {
			return "Make sure your checksum is a number!";
		}

		/**
		 * Does the student exist? It is important to check this for the
		 * following reason: If you delete a user who is not in the database,
		 * the query will not fail and the programflow will continue and will
		 * result in a "Student has been successfully deleted. By checking if
		 * the students exists, we can show a more verbose error message.
		 */
		Student student = studentService.getStudentByName(name, surname);
		if (student == null) {
			return "The requested student does not exist so can't be deleted.";
		}
		if (student.getChecksum() != checksum) {
			return "Wrong checksum!";
		}

		// The parameters are correct and the student exists, so let's delete
		// him!
		studentService.removeStudentByName(name, surname, checksum);

		return "Student " + name + " " + surname + " has been succesfully deleted.";
	}
}
