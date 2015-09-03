package controllers;

import java.io.*;
import java.net.MalformedURLException;
import java.net.SocketException;
import java.net.URL;
import java.net.URLConnection;
import java.util.Arrays;
import java.util.Collections;
import java.util.Enumeration;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;
import java.util.zip.ZipEntry;
import java.util.zip.ZipException;
import java.util.zip.ZipFile;

import models.AnswerType;
import models.FileServer;
import models.Language;
import models.Question;
import models.Question_Language;
import models.Set_Question;

import org.apache.commons.net.ftp.FTPClient;
import org.codehaus.jackson.node.JsonNodeFactory;
import org.codehaus.jackson.node.ObjectNode;

import controllers.security.SecuredOrganizer;
import controllers.security.SecuredTeacher;

import play.data.DynamicForm;
import play.data.Form;
import play.libs.Json;
import play.mvc.Controller;
import play.mvc.Security;
import play.mvc.Http.MultipartFormData;
import play.mvc.Http.MultipartFormData.FilePart;
import play.mvc.Result;
import utils.LangMessages;
import views.html.organizer.processFiles;
import views.html.organizer.uploadQuestions;

@Security.Authenticated(SecuredOrganizer.class)
public class QuestionsController extends Controller {


    /**********************************************************************************************************
     * Render the upload or write page
     * @return
     *********************************************************************************************************/
	public static Result renderUploadQuestions() {
		return ok(uploadQuestions.render());
	}

    /**********************************************************************************************************
     * Handle the uploading part to a temporary folder
     * @return
     *********************************************************************************************************/
	public static Result questionUploader() {
		MultipartFormData body = request().body().asMultipartFormData();
		FilePart questionFile = body.getFile("file");
		ObjectNode result = Json.newObject();
		if (questionFile != null) {
			try {
				File fileToUnzip = moveFileToTempFolder(questionFile.getFile(),
						questionFile.getFilename());
				File unzipped = extractFolder(fileToUnzip.getAbsolutePath());
				result.put("directory", unzipped.getName());
			} catch (IOException e) {
				result.put("error", e.getMessage());
			}
		}
		return ok(result);
	}

    private static File moveFileToTempFolder(File file, String fileName) throws IOException {
        try {
            new File("questionUploads/").mkdir();
            File f = new File("questionUploads" + File.separator + fileName);
            f.createNewFile();
            FileOutputStream fileOut = new FileOutputStream(f);
            FileInputStream fileIn = new FileInputStream(file);
            byte[] buffer = new byte[1024 * 1024];
            int len;
            while ((len = fileIn.read(buffer)) != -1) {
                fileOut.write(buffer, 0, len);
            }
            fileIn.close();
            fileOut.close();
            return new File("questionUploads" + File.separator + fileName);
        } catch (IOException e) {
            e.printStackTrace();
            throw e;
        }
    }

	public static Result renderProcessFiles(String path) {
		return ok(processFiles.render("questionUploads/" + path));
	}

    /**********************************************************************************************************
     * Render processFiles page: builds the question tree
     * @return
     *********************************************************************************************************/

	/**
	 * Connector script for the Questions Jquery File Tree for processing
	 * uploaded questions
	 *
	 * @return
	 */
	public static Result buildQuestionTree() {
		String search = request().body().asFormUrlEncoded().get("dir")[0];
		//List<Question> questions = Question.find.all();
		List<Question> questions = Question.find.where()
			.icontains("questionLanguages.title", search).findList();

		Collections.sort(questions);
		String out = "";
		out += ("<ul class=\"jqueryFileTree\" style=\"display: none\">");
		out += ("<li><a href=\"#\" rel=\"0\">"
				+ LangMessages.get("uploadQuestions.new") + "</a>");
		for (Question q : questions) {
			out += ("<li class=\"file ext_html\"><a href=\"#\" rel=\"" + q.id
					+ "\">" + q.getTitle() + "</a></li>");
		}
		out += "</ul>";
		return ok(out);

	}

	/**
	 * ajax controller for getting the url data from a question
	 *
	 * @param id
	 * @return
	 */
	public static Result getQuestionInfo(Long id) {
		ObjectNode result = Json.newObject();
		Question question = Question.getQuestion(id);
		result.put("id", id);
		if (question != null) {
			for (Language l : Language.values()) {
				if (question.getQuestionFileName(l) != null) {
					result.put(l.name() + "question",
							"" + question.getQuestionFileName(l));
				} else {
					result.put(l.name() + "question", "");
				}
				if (question.getFeedbackFileName(l) != null) {
					result.put(l.name() + "feedback",
							"" + question.getFeedbackFileName(l));
				} else {
					result.put(l.name() + "feedback", "");
				}
				if (question.getTitle(l) != null) {
					result.put(l.name() + "name", "" + question.getTitle(l));
				} else {
					result.put(l.name() + "name", "");
				}
				result.put("answer", question.answer==null ? "" : question.answer);
				result.put("answerType", question.answerType == null? "noAnswerType" : question.answerType.name());
			}
		} else {
			for (Language l : Language.values()) {
				result.put(l.name() + "question", "");
				result.put(l.name() + "feedback", "");
				result.put(l.name() + "name", "");
				result.put("answer", "");
				result.put("answerType", "noAnswerType");
			}

		}

		return ok(result);
	}

	public static Result viewFile(String file) {
		File f = new File("questionUploads" + File.separator + file);
		return ok(f);
	}

	/**
	 * Ajax controller for setting the question info for a question
	 * This handles question and feedback files in all languages, extra files
	 * answer and answer type
	 * @param id	the id of the question for
	 * @param dir	the name of the directory in which all the uploaded files are situated
	 * @return
	 */

	public static Result setQuestionInfo(Long id, String dir) {

        // Create a new result node
		ObjectNode result = Json.newObject();

        // Get the question by id
		Question question = Question.getQuestion(id);

        // If the question is null: create a new question on a random fileserver
        if (question == null) {
            FileServer fs = FileServer.getAFileServer();
            question = new Question();
            question.save();
            question.server = fs;
        }

        // Bind the post data to the map
		Map<String, String[]> form = request().body().asFormUrlEncoded();

        // Map the language to a question_language
		Map<Language, Question_Language> map = new TreeMap<>();


        // Loop over all languages
		for (Language l : Language.values()) {
			Question_Language ql = question.questionLanguages.get(l);

            // If there isn't a QL object, create one!
            if(ql == null) {
                ql = new Question_Language();
                // Set the questions language to the ... well, language.
                ql.language = l;
                ql.generateRandomFeedbackFileName();
                ql.generateRandomQuestionFileName();
            } else {

            	// for questions that were in the database before the random string was implemented
            	if(ql.randomFeedbackFile == null || ql.randomQuestionFile == null) {
            		ql.generateRandomFeedbackFileName();
            		ql.generateRandomQuestionFileName();
            	}
            }

            // Get the title filled in in the form
            String title = form.get(l.name() + "name")[0];

            // We obviously can't allow a question without a title!
			if (!"".equals(title)) {

                // Set the title to the question-in-the-make
				ql.title = title;

				// Handling questionFile
				String questionFile = form.get(l.name() + "question")[0];

				String extension = "";

                // If we have a non-empty question file
				if (!"".equals(questionFile)) {
					System.err.println("questionfile != empty");
					String questionFileName = "";

                    // Split the index & the name
					try {
						extension = questionFile.substring(questionFile.lastIndexOf('.'));
						questionFileName = questionFile.substring(
                            questionFile.lastIndexOf('/') + 1);
					} catch (StringIndexOutOfBoundsException e) {
						questionFile = "";
                        extension = "";
					}

                    // No HTML file?! Run!
					if(!extension.equals(".html")) {
						questionFile = "";
						result.put(l.name() + "questionERR", LangMessages.get("uploadQuestions.extensionFail"));
					}

					// Contains dir?
					// QuestionFile is a newly uploaded file, it should be
					// transferred to the right server
					if (questionFile.contains(dir)) {
                        File f = new File(questionFile.substring(questionFile.indexOf(dir)));

                        if (question.server.uploadFile(f, question, ql.randomQuestionFile)) {
							result.put(l.name() + "questionOK", LangMessages.get("uploadQuestions.ok"));
							ql.questionFile = questionFileName;
						} else {
							result.put(l.name() + "questionERR", LangMessages.get("uploadQuestions.uploadFail"));
						}
					} else {

						// Check if maybe the user has entered the file name manually
						if(new File(dir + File.separator + questionFile).exists()) {

							File f = new File(dir + File.separator + questionFile);
							if (question.server.uploadFile(f, question, ql.randomQuestionFile)) {
								result.put(l.name() + "questionOK", LangMessages.get("uploadQuestions.ok"));
								ql.questionFile = questionFileName;
							} else {
								result.put(l.name() + "questionERR", LangMessages.get("uploadQuestions.uploadFail"));
							}

						}

					}

					// Todo: WHAT TO DO IF IT ISN'T in QuestionUPLOADS?


				} else {
					ql.questionFile = null;
				}

				// Handling feedbackFile
				String feedbackFile = form.get(l.name() + "feedback")[0];
				String feedbackFileName ="";

				if (!"".equals(feedbackFile)) {

					try {

						extension = feedbackFile.substring(feedbackFile.lastIndexOf('.'));
						feedbackFileName = feedbackFile.substring(
							feedbackFile.lastIndexOf('/') + 1);

					} catch(StringIndexOutOfBoundsException e) {

						extension = "";
						feedbackFile = "";

					}

					if(!".html".equals(extension)) {

						feedbackFile = "";
						result.put(l.name()+ "feedbackErr",LangMessages.get("uploadQuestions.extensionFail"));

					}

					// Question is a newly uploaded question, it should be
					// transferred to the right server
					if (feedbackFile.contains(dir)) {

						File f = new File(feedbackFile.substring(feedbackFile.indexOf(dir)));
						if (question.server.uploadFile(f, question, ql.randomFeedbackFile)) {
							result.put(l.name() + "feedbackOK",
									LangMessages.get("uploadQuestions.ok"));
							ql.feedbackFile = feedbackFileName;
						} else {
							result.put(l.name() + "feedbackERR", LangMessages
									.get("uploadQuestions.uploadFail"));
						}


					} else {

						// Check if the user has entered a feedbackfile manually
						if(new File(dir + File.separator + feedbackFile).exists()) {

							File f = new File(dir + File.separator + feedbackFile);

							if (question.server.uploadFile(f, question, ql.randomFeedbackFile)) {
								result.put(l.name() + "feedbackOK",
										LangMessages.get("uploadQuestions.ok"));
								ql.feedbackFile = feedbackFileName;
							} else {
								result.put(l.name() + "feedbackERR", LangMessages
										.get("uploadQuestions.uploadFail"));
							}

						}
					}


				} else {
					ql.feedbackFile = null;
				}

				map.put(l, ql);

			} else {

				if (ql.id != null) {
					// The question_language id is not null
					// so it is in the db. It should be deleted
					question.questionLanguages.remove(ql.language);
					ql.delete();

				} else {

					// If the question id is not null it is not in the database
					// if a question or feedback file is specified
					// a warning should show telling to specify a name
					if (!form.get(l.name() + "question")[0].equals("")) {
						result.put(l.name() + "questionERR",
								LangMessages.get("uploadQuestions.specifyName"));
					}
					if (!form.get(l.name() + "feedback")[0].equals("")) {
						result.put(l.name() + "feedbackERR",
								LangMessages.get("uploadQuestions.specifyName"));
					}
				}
			}
		}

		if (map.isEmpty()) {
			// No names were specified

			if (Set_Question.find.where().eq("question.id", question.id).findRowCount() == 0) {
				// The question isn't part of a set, we can safely delete it
				question.delete();
			} else {
				// remove all the set_questions related with this question
				List<Set_Question> sqList = Set_Question.find.where().eq("question.id", question.id).findList();
				for(Set_Question sq : sqList) {
					sq.delete();
				}
				question.delete();
			}


		} else {

			// Handle AnswerType
			String[] answerTypeAr = form.get("answertype");
			if(answerTypeAr!=null) {
				question.answerType = AnswerType.valueOf(form.get("answertype")[0]);
			} else {
				result.put("answerTypeERR", LangMessages.get("uploadQuestions.answerTypeErr"));
			}

			//Handle Extra Files
			String[] extraFiles = form.get("extras");

			for(String extraFileName : extraFiles) {

				if (extraFileName.contains(dir)) {

					File f = new File(extraFileName.substring(extraFileName
							.indexOf(dir)));
					question.server.uploadFile(f, question, f.getName());

				} else {

					if(!"".equals(extraFileName) && new File(dir + File.separator + extraFileName).exists()) {
                        File f = new File(dir+"/"+extraFileName);
						question.server.uploadFile(f,question, f.getName());
					}

				}
			}

			//Handle Aswer
			String answer = form.get("answer")[0];

			// We don't want multiple choice answers that are longer than one character
			if(question.answerType == AnswerType.MULTIPLE_CHOICE) {
				answer = answer.toUpperCase();
				if(answer.length() != 1 || ((answer.charAt(0) < 'A') || (answer.charAt(0) > 'A' + AnswerType.MULTIPLE_CHOICE.getNumberOfAnwsers()))) {
					result.put("answerERR", LangMessages.get("uploadQuestions.answerErr"));
				} else {
					// The answer is just fine
					question.answer = answer;
				}
			} else {
				// For a regular expression, no extra check is needed
				question.answer = answer;
			}

			question.questionLanguages = map;
			question.save();
		}
		result.put("id", ""+question.id);
		return ok(result);

	}

	
	/*
	 * Handles the creation of the fileTree used in the processQuestions view.
	 * see http://www.abeautifulsite.net/blog/2008/03/jquery-file-tree/
	 * @return	a series of <li>'s that represent the files contained in the directory specified by the "dir" form data
	 */
	public static Result fileTreeConnector() {
		String dir = request().body().asFormUrlEncoded().get("dir")[0];
		if (dir == null) {
			return null;// should not happen
		}

		if (dir.charAt(dir.length() - 1) == '\\') {
			dir = dir.substring(0, dir.length() - 1) + "/";
		} else if (dir.charAt(dir.length() - 1) != '/') {
			dir += "/";
		}

		try {
			dir = java.net.URLDecoder.decode(dir, "UTF-8");
		} catch (UnsupportedEncodingException e) {
			e.printStackTrace();
		}
		return ok(buildList(dir));
	}

	private static String buildList(String dir) {
		String out = "";
		if (new File(dir).exists()) {
			String[] files = new File(dir).list();
			Arrays.sort(files, String.CASE_INSENSITIVE_ORDER);
			out += ("<ul class=\"jqueryFileTree\" style=\"display: none;\">");
			// All dirs
			for (String file : files) {
				if (new File(dir, file).isDirectory()) {
					out += ("<li class=\"directory collapsed\"><a href=\""
							+ dir + file + "\" rel=\"" + dir + file + "/\">"
							+ file + "</a></li>");
				}
			}
			// All files
			for (String file : files) {
				if (!new File(dir, file).isDirectory()) {
					int dotIndex = file.lastIndexOf('.');
					String ext = dotIndex > 0 ? file.substring(dotIndex + 1)
							: "";
					out += ("<li class=\"file ext_" + ext
							+ "\"><a href=\"/play/"+ dir + file +"\" rel=\"" + dir + file + "\">"
							+ file + "</a></li>");
				}
			}
			out += ("</ul>");
		}
		return out;
	}

	public static Result buildQuestionInfoTree() {

		String out = "<ul class=\"jqueryFileTree\" style=\"display: none;\">";
		String dir = request().body().asFormUrlEncoded().get("dir")[0];
		try {
			Long id = Long.parseLong(dir);
			// The dir is a number, The info of the question with id 'dir'
			// should be shown in the file tree
			Question q = Question.getQuestion(id);
			if (q == null) {
				for (Language l : Language.values()) {
					out += "<li class=\"file\"><a rel=\""
							+ l.name()
							+ "Panel\" href=\"#\">"
							+ LangMessages.get("uploadQuestions.newQuestion"
									+ l.name()) + "</a></li>";
				}
			} else {
				for (Language l : q.questionLanguages.keySet()) {
					String type = q.questionLanguages.get(l).feedbackFile == null && q.questionLanguages.get(l).questionFile == null ? "file" : "directory collapsed";
					String rel = type.equals("file") ? l.name()+"Panel" : "/"+l.name()+"."+q.id+"/";
					out += "<li class=\""+type+"\"><a href=\""+
							"#\" rel=\"" + rel + "\">"
							+ q.questionLanguages.get(l).title + "</a></li>";
				}
				for (Language l : Language.values()) {
					if (!q.questionLanguages.containsKey(l)) {
						out += "<li class=\"file\"><a rel=\""
								+ l.name()
								+ "Panel\" href=\"#\">"
								+ LangMessages
										.get("uploadQuestions.newQuestion"
                                            + l.name()) + "</a></li>";
					}
				}
			}
			out+="<li class=\"file\"><a rel=\"EXTRASPanel\" href=\"#\">"+LangMessages.get("uploadQuestions.addExtras")+"</a></li>";
		} catch (NumberFormatException e) {
			// The "dir" was not a number, so it must be a language directory

			Language l = Language.valueOf(dir.substring(1, dir.indexOf('.')));
			if (l == null) {
				// should not happen
				return badRequest();
			}
			Long id;
			try {
				id = Long.parseLong(dir.substring(dir.lastIndexOf('.') + 1,
						dir.length() - 1));
			} catch (NumberFormatException ex) {
				// Should not happen
				return badRequest();
			}

			Question q = Question.getQuestion(id);

			String extension = "";
			String questionFile = q.questionLanguages.get(l) != null ? q.questionLanguages
					.get(l).questionFile : null;
			String feedbackFile = q.questionLanguages.get(l) != null ? q.questionLanguages
					.get(l).feedbackFile : null;
			// Questionfile handling
			if (questionFile != null) {
				extension = questionFile.substring(questionFile
						.lastIndexOf('.') + 1);
				out += "<li class=\"file ext_" + extension + "\"><a rel=\""
						+ l.name() + "Panel\" href=\"" + q.getQuestionURL(l)
						+ "\">" + questionFile + "</a></li>";
			}

			if (feedbackFile != null) {
				extension = feedbackFile.substring(feedbackFile
						.lastIndexOf('.') + 1);
				out += "<li class=\"file ext_" + extension + "\"><a rel=\""
						+ l.name() + "Panel\" href=\"" + q.getFeedbackURL(l)
						+ "\">" + feedbackFile + "</a></li>";
			}
		}
		out += "</ul>";
		return ok(out);
	}

	// Source:
	// http://stackoverflow.com/questions/1399126/java-util-zip-recreating-directory-structure
	private static File extractFolder(String zipFile) throws ZipException,
			IOException {
		int BUFFER = 2048;
		File file = new File(zipFile);

		ZipFile zip = new ZipFile(file);
		String newPath = zipFile.substring(0, zipFile.length() - 4);

		File ret = new File(newPath);
		ret.mkdir();
		Enumeration zipFileEntries = zip.entries();

		// Process each entry
		while (zipFileEntries.hasMoreElements()) {
			// grab a zip file entry
			ZipEntry entry = (ZipEntry) zipFileEntries.nextElement();
			String currentEntry = entry.getName();
			File destFile = new File(newPath, currentEntry);
			// destFile = new File(newPath, destFile.getName());
			File destinationParent = destFile.getParentFile();

			// create the parent directory structure if needed
			destinationParent.mkdirs();

			if (!entry.isDirectory()) {
				BufferedInputStream is = new BufferedInputStream(
						zip.getInputStream(entry));
				int currentByte;
				// establish buffer for writing file
				byte data[] = new byte[BUFFER];

				// write the current file to disk
				FileOutputStream fos = new FileOutputStream(destFile);
				BufferedOutputStream dest = new BufferedOutputStream(fos,
						BUFFER);

				// read and write until last byte is encountered
				while ((currentByte = is.read(data, 0, BUFFER)) != -1) {
					dest.write(data, 0, currentByte);
				}
				dest.flush();
				dest.close();
				is.close();
			}

			if (currentEntry.endsWith(".zip")) {
				// found a zip file, try to open
				extractFolder(destFile.getAbsolutePath());
			}
		}
		return ret;
	}

    /*********************************************************************************
     * Get question content
     *********************************************************************************/
    public static Result buildQuestionInfoTreeWithoutLinks() {

        String out = "<ul class=\"jqueryFileTree\" style=\"display: none;\">";
        String dir = request().body().asFormUrlEncoded().get("dir")[0];
        try {
            Long id = Long.parseLong(dir);
            // The dir is a number, The info of the question with id 'dir'
            // should be shown in the file tree
            Question q = Question.getQuestion(id);
            if (q == null) {
                for (Language l : Language.values()) {
                    out += "<li class=\"file\"><a rel=\""
                        + l.name() + "\" href=\"#\">"
                        + LangMessages.get("uploadQuestions.newQuestion"
                        + l.name()) + "</a></li>";
                }
            } else {
                for (Language l : q.questionLanguages.keySet()) {
                    out += "<li class=\"file\"><a href=\""+
                        "#\" rel=\"" + l.name() + "-" + id + "\">"
                        + q.questionLanguages.get(l).title + "</a></li>";
                }
                for (Language l : Language.values()) {
                    if (!q.questionLanguages.containsKey(l)) {
                        out += "<li class=\"file\"><a rel=\""
                            + l.name() + "-" + id + "\" href=\"#\">"
                            + LangMessages
                            .get("uploadQuestions.newQuestion"
                                + l.name()) + "</a></li>";
                    }
                }
            }
        } catch (NumberFormatException e) {

        }
        out += "</ul>";
        return ok(out);
    }

    public static Result getQuestionContents(String file) {
        ObjectNode result = Json.newObject();

        if(file.contains("-")) {
            String[] splitted = file.split("-");
            String name = splitted[0];
            Long id = Long.parseLong(splitted[1]);

            Question q = Question.getQuestion(id);

            result.put("id", q.id);
            result.put("language", name);

            result.put("answertype", q.answerType.name());
            result.put("answer", q.answer);

            // Does this file exist?
            if(q.questionLanguages.containsKey(Language.valueOf(name))) { // Yup, so get it!
                result.put("title", q.getTitle(Language.valueOf(name)));
                result.put("question", getText(q.getQuestionURL(Language.valueOf(name)).toString()));
                result.put("feedback", getText(q.getFeedbackURL(Language.valueOf(name)).toString()));
            } else { // Nope: empty fields plox!
                result.put("name", "");
                result.put("question", "");
                result.put("feedback", "");
            }
        } else {
            result.put("id", -1);
            result.put("name", "");
            result.put("question", "");
            result.put("feedback", "");
            result.put("language", file);
        }

        return ok(result.toString());
    }

    // Sauce:
    public static String getText(String url) {
        try {
            URL website = new URL(url);
            URLConnection connection = website.openConnection();
            BufferedReader in = new BufferedReader(
                new InputStreamReader(
                    connection.getInputStream()));

            StringBuilder response = new StringBuilder();
            String inputLine;

            while ((inputLine = in.readLine()) != null)
                response.append(inputLine);

            in.close();

            return response.toString();

        } catch (MalformedURLException e) {
            e.printStackTrace();
        } catch (IOException e) {
            e.printStackTrace();
        }
        return "";
    }

    public static Result updateQuestion() {

        ObjectNode result = Json.newObject();
        boolean error = false;

        // Bind the post data to the map
        Map<String, String[]> form = request().body().asFormUrlEncoded();

        // Input validation!
        if("".equals(form.get("title")[0].trim())) {
            error = true;
            result.put("error", "true");
            result.put("titleError", LangMessages.get("uploadQuestions.wysiwyg.titleError"));
        }
        if("".equals(form.get("answertype")[0].trim())) {
            error = true;
            result.put("error", "true");
            result.put("answertypeError", LangMessages.get("uploadQuestions.wysiwyg.answertypeError"));
        }
        if("".equals(form.get("answer")[0].trim())) {
            error = true;
            result.put("error", "true");
            result.put("answerError", LangMessages.get("uploadQuestions.wysiwyg.answerError"));
        }

        if("".equals(form.get("questionEditor")[0].trim())) {
            error = true;
            result.put("error", "true");
            result.put("questionError", LangMessages.get("uploadQuestions.wysiwyg.questionError"));
        }
        if("".equals(form.get("feedbackEditor")[0].trim())) {
            error = true;
            result.put("error", "true");
            result.put("feedbackError", LangMessages.get("uploadQuestions.wysiwyg.feedbackError"));
        }
        if(AnswerType.valueOf(form.get("answertype")[0]) == AnswerType.MULTIPLE_CHOICE) {
            String answer = form.get("answer")[0].toUpperCase();

            if(answer.length() != 1 || ((answer.charAt(0) < 'A') || (answer.charAt(0) > 'A' + AnswerType.MULTIPLE_CHOICE.getNumberOfAnwsers()))) {
                error = true;
                result.put("error", "true");
                result.put("answerError", LangMessages.get("uploadQuestions.wysiwyg.answerError"));
            }
        }

        if(error) { // There were errors: return it!

            return ok(result.toString());

        } else { // No errors: continue!

            Language language = Language.valueOf(form.get("language")[0]);

            // Question doesn't exist yet! Add a new question.
            if(form.get("id")[0].equals("-1")) {

                FileServer fs = FileServer.getAFileServer();
                Question question = new Question();
                question.server = fs;
                question.answer = form.get("answer")[0];
                question.answerType = AnswerType.valueOf(form.get("answertype")[0]);

                Question_Language questionLanguage = new Question_Language();
                questionLanguage.title = form.get("title")[0];
                questionLanguage.language = language;
                questionLanguage.questionFile = "question_" + language.getOfficialCode() + ".html";
                questionLanguage.feedbackFile = "feedback_" + language.getOfficialCode() + ".html";
                questionLanguage.generateRandomQuestionFileName();
                questionLanguage.generateRandomFeedbackFileName();

                Map<Language, Question_Language> map = new TreeMap<>();
                map.put(language, questionLanguage);
                question.questionLanguages = map;

                question.save();

                try {
                    uploadChanges(fs, form.get("questionEditor")[0], form.get("feedbackEditor")[0], question, questionLanguage);
                } catch (FileNotFoundException e) {
                    result.put("error", "true");
                    result.put("generalError", LangMessages.get("uploadQuestions.wysiwyg.fileError"));
                    return ok(result.toString());
                }

                result.put("id", question.id);
                return ok(result.toString());

            } else {

                Long id = Long.parseLong(form.get("id")[0]);
                Question question = Question.getQuestion(id);
                FileServer fs = question.server;

                result.put("id", id);

                // Update the answer & the types
                question.answer = form.get("answer")[0];
                question.answerType = AnswerType.valueOf(form.get("answertype")[0]);

                Map<Language, Question_Language> map = new TreeMap<>();
                for(Language l : question.questionLanguages.keySet()) {
                    map.put(l, question.questionLanguages.get(l));
                }

                Question_Language questionLanguage;

                if(!question.questionLanguages.containsKey(language)) { // Language doesn't exist yet! Add a new questionlanguae

                    questionLanguage = new Question_Language();

                    map.put(language, questionLanguage);

                    questionLanguage.title = form.get("title")[0];
                    questionLanguage.language = language;
                    questionLanguage.generateRandomQuestionFileName();
                    questionLanguage.generateRandomFeedbackFileName();

                } else {
                    questionLanguage = map.get(language);
                }

                questionLanguage.title = form.get("title")[0];
                questionLanguage.questionFile = "question_" + language.getOfficialCode() + ".html";
                questionLanguage.feedbackFile = "feedback_" + language.getOfficialCode() + ".html";

                question.questionLanguages = map;

                // Save it!
                question.save();

                try {
                    uploadChanges(fs, form.get("questionEditor")[0], form.get("feedbackEditor")[0], question, questionLanguage);
                } catch (FileNotFoundException e) {
                    result.put("error", "true");
                    result.put("generalError", LangMessages.get("uploadQuestions.wysiwyg.fileError"));
                    return ok(result.toString());
                }

                return ok(result.toString());

            }

        }
    }

    public static void uploadChanges(FileServer fs, String questionContent, String feedbackContent, Question question, Question_Language questionLanguage) throws FileNotFoundException {
        PrintWriter questionOut = new PrintWriter("tempQuestion.html");
        PrintWriter feedbackOut = new PrintWriter("tempFeedback.html");

        questionOut.print(questionContent);
        feedbackOut.print(feedbackContent);

        if(questionOut != null) {
            questionOut.close();
        }
        if(feedbackOut != null) {
            feedbackOut.close();
        }

        File questionFile = new File("tempQuestion.html");
        File feedbackFile = new File("tempFeedback.html");

        fs.uploadFile(questionFile, question, questionLanguage.randomQuestionFile);
        fs.uploadFile(feedbackFile, question, questionLanguage.randomFeedbackFile);

        questionFile.delete();
        feedbackFile.delete();
    }
}
