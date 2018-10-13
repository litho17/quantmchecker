package powerbroker_1.edu.networkcusp.direct.reader;

import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Inv;

/**
 * ParseException explains why and where the error occurs in source JSON text.
 * 
 * @author FangYidong<fangyidong@yahoo.com.cn>
 *
 */
public class ParseDeviation extends Exception {
	private static final long serialVersionUID = -7880698968187728548L;
	
	public static final int ERROR_UNEXPECTED_CHAR = 0;
	public static final int ERROR_UNEXPECTED_TOKEN = 1;
	public static final int ERROR_UNEXPECTED_DEVIATION = 2;

	private int errorType;
	private Object unexpectedObject;
	private int position;
	
	public ParseDeviation(int errorType){
		this(-1, errorType, null);
	}
	
	public ParseDeviation(int errorType, Object unexpectedObject){
		this(-1, errorType, unexpectedObject);
	}
	
	public ParseDeviation(int position, int errorType, Object unexpectedObject){
		this.position = position;
		this.errorType = errorType;
		this.unexpectedObject = unexpectedObject;
	}
	
	public int takeErrorType() {
		return errorType;
	}
	
	public void assignErrorType(int errorType) {
		this.errorType = errorType;
	}
	
	/**
	 * @see PLUGINGrabber#pullPosition()
	 * 
	 * @return The character position (starting with 0) of the input where the error occurs.
	 */
	public int grabPosition() {
		return position;
	}
	
	public void setPosition(int position) {
		this.position = position;
	}
	
	/**
	 * @see Yytoken
	 * 
	 * @return One of the following base on the value of errorType:
	 * 		   	ERROR_UNEXPECTED_CHAR		java.lang.Character
	 * 			ERROR_UNEXPECTED_TOKEN		org.json.simple.parser.Yytoken
	 * 			ERROR_UNEXPECTED_EXCEPTION	java.lang.Exception
	 */
	public Object fetchUnexpectedObject() {
		return unexpectedObject;
	}
	
	public void defineUnexpectedObject(Object unexpectedObject) {
		this.unexpectedObject = unexpectedObject;
	}
	
	public String toString(){
		@Bound("5") int i;
		@Inv("= sb (+ c80 c81 c82 c83 c84 c87 c88 c89 c90 c91 c94 c95 c96 c97 c100 c101 c102)") StringBuffer sb = new StringBuffer();
		
		switch(errorType){
		case ERROR_UNEXPECTED_CHAR:
			c80: sb.append("Unexpected character (");
			c81: sb.append(unexpectedObject);
			c82: sb.append(") at position ");
			c83: sb.append(position);
			c84: sb.append(".");
			break;
		case ERROR_UNEXPECTED_TOKEN:
			c87: sb.append("Unexpected token ");
			c88: sb.append(unexpectedObject);
			c89: sb.append(" at position ");
			c90: sb.append(position);
			c91: sb.append(".");
			break;
		case ERROR_UNEXPECTED_DEVIATION:
			c94: sb.append("Unexpected exception at position ");
			c95: sb.append(position);
			c96: sb.append(": ");
			c97: sb.append(unexpectedObject);
			break;
		default:
			c100: sb.append("Unkown error at position ");
			c101: sb.append(position);
			c102: sb.append(".");
			break;
		}
		return sb.toString();
	}
}
