package tictactoe.src;

import utils.TextIO;

public class HumanPlayer extends Player {

    /**
     * Creates a new human player object.
     */
    /*@ requires name != null;
        requires mark == Mark.XX || mark == Mark.OO;
    @*/
    public HumanPlayer(String name, Mark mark) {
        super(name, mark);
    }


    /**
     * Asks the user to input the field where to place the next mark. This is
     * done using the standard input/output.
     * @param board the game board
     * @return the player's chosen field
     */
    /*@ requires board != null;
        ensures board.isField(\result) && board.getField(\result) == Mark.EMPTY;
    @*/
    public int determineMove(Board board) {
        String prompt = "> " + getName() + " (" + getMark().toString() + ")"
                + ", what is your choice? ";

        System.out.println(prompt);
        int choice = TextIO.getInt();
        boolean valid = board.isField(choice) && board.isEmptyField(choice);
        while (!valid) {
            try{
                throw new InvalidChoiceException("Invalid Choice Exception: field " + choice + " is no valid choice.");
            }catch(InvalidChoiceException e){
                System.out.println(e.getMessage());
                System.out.println(prompt);
                choice = TextIO.getInt();
                valid = board.isField(choice) && board.isEmptyField(choice);
            }
        }
        return choice;
    }
}
