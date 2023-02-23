import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import tictactoe.src.Board;
import tictactoe.src.Mark;

public class BoardTest {

    Board board;

    @BeforeEach
    public void setup(){
        board = new Board();
    }

    @Test
    public void BoardInitTest(){
        //Testing if the board initializes correctly
        for(int i=0; i<Board.DIM*Board.DIM; i++){
            Assertions.assertTrue(board.isEmptyField(i));
        }
    }

    @Test
    public void indexTest(){
        //Tests if indexes (based on row and col number) are converted correctly into
        //a one-digit index
        Assertions.assertEquals(5,board.index(1,2));
        Assertions.assertNotEquals(8, board.index(2,3));
    }

    @Test
    public void isEmptyFieldTest(){
        //Tests if starting board is empty. After an alteration, state of
        //the board is rechecked.
        for(int i=0; i<Board.DIM*Board.DIM; i++){
            Assertions.assertTrue(board.isEmptyField(i));
        }
        board.setField(7, Mark.XX);
        Assertions.assertFalse(board.isEmptyField(7));
    }

    @Test
    public void hasColumnTest(){
        //Tests if, after inputting 3 of the same mark in a column,
        //the board class recognizes this and acts accordingly.
        board.setField(0, Mark.XX);
        board.setField(4, Mark.OO);
        board.setField(3, Mark.XX);
        board.setField(5, Mark.OO);
        board.setField(6, Mark.XX);
        Assertions.assertTrue(board.hasColumn(Mark.XX));
        Assertions.assertFalse(board.hasColumn(Mark.OO));
    }

    @Test
    public void hasRowTest(){
        //Tests if, after inputting 3 of the same mark in a row,
        //the board class recognizes this and acts accordingly.
        board.setField(0, Mark.XX);
        board.setField(4, Mark.OO);
        board.setField(1, Mark.XX);
        board.setField(5, Mark.OO);
        board.setField(2, Mark.XX);
        Assertions.assertTrue(board.hasRow(Mark.XX));
        Assertions.assertFalse(board.hasRow(Mark.OO));
    }

    @Test
    public void hasDiagonalTest(){
        //Tests if, after inputting 3 of the same mark in a diagonal,
        //the board class recognizes this and acts accordingly.
        board.setField(0,Mark.XX);
        board.setField(1,Mark.OO);
        board.setField(4,Mark.XX);
        board.setField(3,Mark.OO);
        board.setField(8,Mark.XX);
        Assertions.assertTrue(board.hasDiagonal(Mark.XX));
        Assertions.assertFalse(board.hasDiagonal(Mark.OO));
    }
}
