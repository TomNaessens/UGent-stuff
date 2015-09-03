
package stemmer;

public class Exceptions {

    public static class IncorrectPIN extends Exception {
        protected static final long serialVersionUID = 1;
        public IncorrectPIN(String pin) {
            super("Incorrect PIN: " + pin);
        }
    }

    public static class EIDNotFound extends Exception {
        protected static final long serialVersionUID = 1;
        public EIDNotFound(Throwable cause) {
            super(cause);
        }
    }

    public static class RetrievalFailed extends Exception {
        protected static final long serialVersionUID = 1;
        public RetrievalFailed(Throwable cause) {
            super(cause);
        }
    }

    public static class DeliveringFailed extends Exception {
        protected static final long serialVersionUID = 1;
        public DeliveringFailed(Throwable cause) {
            super(cause);
        }
    }

    public static class DuplicateVote extends Exception {
        protected static final long serialVersionUID = 1;
        public DuplicateVote() {
            super();
        }
    }

}
