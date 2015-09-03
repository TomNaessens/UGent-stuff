ALTER TABLE file_server RENAME questions_link TO question_folder;
ALTER TABLE file_server ADD COLUMN public_link varchar(255);
