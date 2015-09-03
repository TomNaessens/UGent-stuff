# --- Created by Ebean DDL
# To stop Ebean DDL generation, remove this comment and start using Evolutions

# --- !Ups

create table admin (
  bebras_id                 varchar(255) not null,
  password                  varchar(255),
  first_password            varchar(255),
  email                     varchar(255),
  first_name                varchar(255),
  last_name                 varchar(255),
  gender                    integer,
  language                  integer not null,
  timestamp                 timestamp,
  constraint ck_admin_gender check (gender in (0,1)),
  constraint ck_admin_language check (language in (0,1,2,3)),
  constraint pk_admin primary key (bebras_id))
;

create table anonymous_user_stats (
  id                        bigint not null,
  number_correct            integer,
  number_wrong              integer,
  question_id               bigint,
  set_id                    bigint,
  constraint pk_anonymous_user_stats primary key (id))
;

create table answer_history (
  id                        bigint not null,
  history_id                bigint,
  question_id               bigint,
  given_answer              varchar(255),
  constraint pk_answer_history primary key (id))
;

create table class (
  id                        bigint not null,
  name                      varchar(255),
  level                     integer,
  begin_year                integer,
  school_id                 bigint,
  teacher_bebras_id         varchar(255),
  constraint ck_class_level check (level in (0,1,2,3)),
  constraint pk_class primary key (id))
;

create table class_competition (
  id                        bigint not null,
  current_class_id          bigint,
  competition_id            bigint,
  is_open                   smallint,
  constraint pk_class_competition primary key (id))
;

create table competition (
  id                        bigint not null,
  is_open                   smallint,
  comp_type                 integer,
  constraint ck_competition_comp_type check (comp_type in (0,1,2)),
  constraint pk_competition primary key (id))
;

create table competition_language (
  id                        bigint not null,
  competition_id            bigint not null,
  language                  integer,
  title                     varchar(255),
  constraint ck_competition_language_language check (language in (0,1,2,3)),
  constraint pk_competition_language primary key (id))
;

create table file_server (
  id                        bigint not null,
  host                      varchar(255),
  port                      integer,
  question_folder           varchar(255),
  public_link               varchar(255),
  username                  varchar(255),
  pass                      varchar(255),
  constraint pk_file_server primary key (id))
;

create table organizer (
  bebras_id                 varchar(255) not null,
  password                  varchar(255),
  first_password            varchar(255),
  email                     varchar(255),
  first_name                varchar(255),
  last_name                 varchar(255),
  gender                    integer,
  language                  integer not null,
  timestamp                 timestamp,
  constraint ck_organizer_gender check (gender in (0,1)),
  constraint ck_organizer_language check (language in (0,1,2,3)),
  constraint pk_organizer primary key (bebras_id))
;

create table participation_history (
  id                        bigint not null,
  participant_bebras_id     varchar(255),
  competition_id            bigint,
  question_set_id           bigint,
  start_time                timestamp,
  end_time                  timestamp,
  extra_time                bigint,
  constraint pk_participation_history primary key (id))
;

create table pupil (
  bebras_id                 varchar(255) not null,
  password                  varchar(255),
  first_password            varchar(255),
  email                     varchar(255),
  first_name                varchar(255),
  last_name                 varchar(255),
  gender                    integer,
  language                  integer not null,
  timestamp                 timestamp,
  current_class_id          bigint,
  previous_class_id         bigint,
  start_time                integer,
  is_finished               boolean,
  deactivated               boolean,
  date_of_birth             timestamp,
  constraint ck_pupil_gender check (gender in (0,1)),
  constraint ck_pupil_language check (language in (0,1,2,3)),
  constraint pk_pupil primary key (bebras_id))
;

create table question (
  id                        bigint not null,
  official_id               varchar(255),
  author                    varchar(255),
  answer_type               integer,
  answer                    varchar(255),
  server_id                 bigint,
  constraint ck_question_answer_type check (answer_type in (0,1)),
  constraint pk_question primary key (id))
;

create table question_language (
  id                        bigint not null,
  question_id               bigint not null,
  title                     varchar(255),
  question_file             varchar(255),
  random_question_file      varchar(255),
  random_feedback_file      varchar(255),
  feedback_file             varchar(255),
  language                  integer,
  constraint ck_question_language_language check (language in (0,1,2,3)),
  constraint pk_question_language primary key (id))
;

create table school (
  id                        bigint not null,
  name                      varchar(255),
  city                      varchar(255),
  zip_code                  varchar(255),
  country                   varchar(255),
  street                    varchar(255),
  number                    varchar(255),
  constraint pk_school primary key (id))
;

create table set (
  id                        bigint not null,
  time_limit                integer,
  is_hidden                 boolean,
  level                     integer,
  length                    integer,
  is_restricted             integer,
  constraint ck_set_level check (level in (0,1,2,3)),
  constraint ck_set_is_restricted check (is_restricted in (0,1,2)),
  constraint pk_set primary key (id))
;

create table set_language (
  id                        bigint not null,
  set_id                    bigint not null,
  language                  integer,
  title                     varchar(255),
  constraint ck_set_language_language check (language in (0,1,2,3)),
  constraint pk_set_language primary key (id))
;

create table set_question (
  id                        bigint not null,
  difficulty                integer,
  correct_points            smallint,
  incorrect_points          smallint,
  question_id               bigint,
  set_id                    bigint,
  constraint ck_set_question_difficulty check (difficulty in (0,1,2)),
  constraint pk_set_question primary key (id))
;

create table teacher (
  bebras_id                 varchar(255) not null,
  password                  varchar(255),
  first_password            varchar(255),
  email                     varchar(255),
  first_name                varchar(255),
  last_name                 varchar(255),
  gender                    integer,
  language                  integer not null,
  timestamp                 timestamp,
  telephone                 varchar(255),
  constraint ck_teacher_gender check (gender in (0,1)),
  constraint ck_teacher_language check (language in (0,1,2,3)),
  constraint pk_teacher primary key (bebras_id))
;

create table token (
  token                     varchar(255) not null,
  bebras_id                 varchar(255),
  date_of_creation          timestamp,
  email                     varchar(255),
  constraint pk_token primary key (token))
;


create table competition_set (
  competition_id                 bigint not null,
  set_id                         bigint not null,
  constraint pk_competition_set primary key (competition_id, set_id))
;

create table teacher_school (
  teacher_bebras_id              varchar(255) not null,
  school_id                      bigint not null,
  constraint pk_teacher_school primary key (teacher_bebras_id, school_id))
;
create sequence admin_seq;

create sequence anonymous_user_stats_seq;

create sequence answer_history_seq;

create sequence class_seq;

create sequence class_competition_seq;

create sequence competition_seq;

create sequence competition_language_seq;

create sequence file_server_seq;

create sequence organizer_seq;

create sequence participation_history_seq;

create sequence pupil_seq;

create sequence question_seq;

create sequence question_language_seq;

create sequence school_seq;

create sequence set_seq;

create sequence set_language_seq;

create sequence set_question_id_seq;

create sequence teacher_seq;

create sequence token_seq;

alter table anonymous_user_stats add constraint fk_anonymous_user_stats_questi_1 foreign key (question_id) references question (id) on delete restrict on update restrict;
create index ix_anonymous_user_stats_questi_1 on anonymous_user_stats (question_id);
alter table anonymous_user_stats add constraint fk_anonymous_user_stats_set_2 foreign key (set_id) references set (id) on delete restrict on update restrict;
create index ix_anonymous_user_stats_set_2 on anonymous_user_stats (set_id);
alter table answer_history add constraint fk_answer_history_history_3 foreign key (history_id) references participation_history (id) on delete restrict on update restrict;
create index ix_answer_history_history_3 on answer_history (history_id);
alter table answer_history add constraint fk_answer_history_question_4 foreign key (question_id) references question (id) on delete restrict on update restrict;
create index ix_answer_history_question_4 on answer_history (question_id);
alter table class add constraint fk_class_school_5 foreign key (school_id) references school (id) on delete restrict on update restrict;
create index ix_class_school_5 on class (school_id);
alter table class add constraint fk_class_teacher_6 foreign key (teacher_bebras_id) references teacher (bebras_id) on delete restrict on update restrict;
create index ix_class_teacher_6 on class (teacher_bebras_id);
alter table class_competition add constraint fk_class_competition_currentCl_7 foreign key (current_class_id) references class (id) on delete restrict on update restrict;
create index ix_class_competition_currentCl_7 on class_competition (current_class_id);
alter table class_competition add constraint fk_class_competition_competiti_8 foreign key (competition_id) references competition (id) on delete restrict on update restrict;
create index ix_class_competition_competiti_8 on class_competition (competition_id);
alter table competition_language add constraint fk_competition_language_compet_9 foreign key (competition_id) references competition (id) on delete restrict on update restrict;
create index ix_competition_language_compet_9 on competition_language (competition_id);
alter table participation_history add constraint fk_participation_history_part_10 foreign key (participant_bebras_id) references pupil (bebras_id) on delete restrict on update restrict;
create index ix_participation_history_part_10 on participation_history (participant_bebras_id);
alter table participation_history add constraint fk_participation_history_comp_11 foreign key (competition_id) references competition (id) on delete restrict on update restrict;
create index ix_participation_history_comp_11 on participation_history (competition_id);
alter table participation_history add constraint fk_participation_history_ques_12 foreign key (question_set_id) references set (id) on delete restrict on update restrict;
create index ix_participation_history_ques_12 on participation_history (question_set_id);
alter table pupil add constraint fk_pupil_currentClass_13 foreign key (current_class_id) references class (id) on delete restrict on update restrict;
create index ix_pupil_currentClass_13 on pupil (current_class_id);
alter table pupil add constraint fk_pupil_previousClass_14 foreign key (previous_class_id) references class (id) on delete restrict on update restrict;
create index ix_pupil_previousClass_14 on pupil (previous_class_id);
alter table question add constraint fk_question_server_15 foreign key (server_id) references file_server (id) on delete restrict on update restrict;
create index ix_question_server_15 on question (server_id);
alter table question_language add constraint fk_question_language_question_16 foreign key (question_id) references question (id) on delete restrict on update restrict;
create index ix_question_language_question_16 on question_language (question_id);
alter table set_language add constraint fk_set_language_set_17 foreign key (set_id) references set (id) on delete restrict on update restrict;
create index ix_set_language_set_17 on set_language (set_id);
alter table set_question add constraint fk_set_question_question_18 foreign key (question_id) references question (id) on delete restrict on update restrict;
create index ix_set_question_question_18 on set_question (question_id);
alter table set_question add constraint fk_set_question_set_19 foreign key (set_id) references set (id) on delete restrict on update restrict;
create index ix_set_question_set_19 on set_question (set_id);



alter table competition_set add constraint fk_competition_set_competitio_01 foreign key (competition_id) references competition (id) on delete restrict on update restrict;

alter table competition_set add constraint fk_competition_set_set_02 foreign key (set_id) references set (id) on delete restrict on update restrict;

alter table teacher_school add constraint fk_teacher_school_teacher_01 foreign key (teacher_bebras_id) references teacher (bebras_id) on delete restrict on update restrict;

alter table teacher_school add constraint fk_teacher_school_school_02 foreign key (school_id) references school (id) on delete restrict on update restrict;

# --- !Downs

SET REFERENTIAL_INTEGRITY FALSE;

drop table if exists admin;

drop table if exists anonymous_user_stats;

drop table if exists answer_history;

drop table if exists class;

drop table if exists class_competition;

drop table if exists competition;

drop table if exists competition_set;

drop table if exists competition_language;

drop table if exists file_server;

drop table if exists organizer;

drop table if exists participation_history;

drop table if exists pupil;

drop table if exists question;

drop table if exists question_language;

drop table if exists school;

drop table if exists set;

drop table if exists set_language;

drop table if exists set_question;

drop table if exists teacher;

drop table if exists teacher_school;

drop table if exists token;

SET REFERENTIAL_INTEGRITY TRUE;

drop sequence if exists admin_seq;

drop sequence if exists anonymous_user_stats_seq;

drop sequence if exists answer_history_seq;

drop sequence if exists class_seq;

drop sequence if exists class_competition_seq;

drop sequence if exists competition_seq;

drop sequence if exists competition_language_seq;

drop sequence if exists file_server_seq;

drop sequence if exists organizer_seq;

drop sequence if exists participation_history_seq;

drop sequence if exists pupil_seq;

drop sequence if exists question_seq;

drop sequence if exists question_language_seq;

drop sequence if exists school_seq;

drop sequence if exists set_seq;

drop sequence if exists set_language_seq;

drop sequence if exists set_question_id_seq;

drop sequence if exists teacher_seq;

drop sequence if exists token_seq;

