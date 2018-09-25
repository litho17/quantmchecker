package braidit_1.com.cyberpointllc.stac.jack.direct.grabber;

import plv.colorado.edu.quantmchecker.qual.Inv;

/**
 * ParseException explains why and where the error occurs in source JSON text.
 * 
 * @author FangYidong<fangyidong@yahoo.com.cn>
 *
 */
public class ParseException extends Exception {
	private static final long serialVersionUID = -7880698968187728548L;
	
	public static final int ERROR_UNEXPECTED_CHAR = 0;
	public static final int ERROR_UNEXPECTED_TOKEN = 1;
	public static final int ERROR_UNEXPECTED_EXCEPTION = 2;

	private int errorType;
	private Object unexpectedObject;
	private int position;
	
	public ParseException(int errorType){
		this(-1, errorType, null);
	}
	
	public ParseException(int errorType, Object unexpectedObject){
		this(-1, errorType, unexpectedObject);
	}
	
	public ParseException(int position, int errorType, Object unexpectedObject){
		this.position = position;
		this.errorType = errorType;
		this.unexpectedObject = unexpectedObject;
	}
	
	public int fetchErrorType() {
		return errorType;
	}
	
	public void defineErrorType(int errorType) {
		this.errorType = errorType;
	}
	
	/**
	 * @see OBJNOTEParser#pullPosition()
	 * 
	 * @return The character position (starting with 0) of the input where the error occurs.
	 */
	public int obtainPosition() {
		return position;
	}
	
	public void assignPosition(int position) {
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
	public Object grabUnexpectedObject() {
		return unexpectedObject;
	}
	
	public void fixUnexpectedObject(Object unexpectedObject) {
		this.unexpectedObject = unexpectedObject;
	}
	
	public String toString(){
		@Inv("= self (+ c78 c79 c80 c81 c82 c85 c86 c87 c88 c89 c92 c93 c94 c95 c98 c99 c100)") StringBuffer sb = new StringBuffer();
		
		switch(errorType){
		case ERROR_UNEXPECTED_CHAR:
			c78: sb.append("Unexpected character (");
			c79: sb.append(unexpectedObject);
			c80: sb.append(") at position ");
			c81: sb.append(position);
			c82: sb.append(".");
			break;
		case ERROR_UNEXPECTED_TOKEN:
			c85: sb.append("Unexpected token ");
			c86: sb.append(unexpectedObject);
			c87: sb.append(" at position ");
			c88: sb.append(position);
			c89: sb.append(".");
			break;
		case ERROR_UNEXPECTED_EXCEPTION:
			c92: sb.append("Unexpected exception at position ");
			c93: sb.append(position);
			c94: sb.append(": ");
			c95: sb.append(unexpectedObject);
			break;
		default:
			c98: sb.append("Unkown error at position ");
			c99: sb.append(position);
			c100: sb.append(".");
			break;
		}
		return sb.toString();
	}
}
