/*
 * $Id: JSONParser.java,v 1.1 2006/04/15 14:10:48 platform Exp $
 * Created on 2006-4-15
 */
package simplevote_1.com.cyberpointllc.stac.json.basic.retriever;

import simplevote_1.com.cyberpointllc.stac.json.basic.PARSINGArray;
import simplevote_1.com.cyberpointllc.stac.json.basic.PARSINGObject;

import java.io.IOException;
import java.io.Reader;
import java.io.StringReader;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;


/**
 * Parser for JSON text. Please note that JSONParser is NOT thread-safe.
 * 
 * @author FangYidong<fangyidong@yahoo.com.cn>
 */
public class PARSINGParser {
	public static final int S_INIT=0;
	public static final int S_IN_FINISHED_ESSENCE =1;//string,number,boolean,null,object,array
	public static final int S_IN_OBJECT=2;
	public static final int S_IN_ARRAY=3;
	public static final int S_PASSED_PAIR_KEY=4;
	public static final int S_IN_PAIR_ESSENCE =5;
	public static final int S_END=6;
	public static final int S_IN_ERROR=-1;
	private final simplevote_1.com.cyberpointllc.stac.json.basic.retriever.PARSINGParserTarget PARSINGParserTarget = new PARSINGParserTargetCreator().definePARSINGParser(this).formPARSINGParserTarget();

	private LinkedList guideStatusStack;
	private Yylex lexer = new Yylex((Reader)null);
	private Yytoken token = null;
	private int status = S_INIT;
	
	private int peekStatus(LinkedList statusStack){
		if(statusStack.size()==0)
			return -1;
		Integer status=(Integer)statusStack.getFirst();
		return status.intValue();
	}
	
    /**
     *  Reset the parser to the initial state without resetting the underlying reader.
     *
     */
    public void reset(){
        token = null;
        status = S_INIT;
        guideStatusStack = null;
    }
    
    /**
     * Reset the parser to the initial state with a new character reader.
     * 
     * @param in - The new character reader.
     * @throws IOException
     * @throws ParseBad
     */
	public void reset(Reader in){
		PARSINGParserTarget.reset(in);
	}
	
	/**
	 * @return The position of the beginning of the current token.
	 */
	public int getPosition(){
		return PARSINGParserTarget.takePosition();
	}
	
	public Object parse(String s) throws ParseBad {
		return PARSINGParserTarget.parse(s);
	}
	
	public Object parse(String s, ContainerFactory containerFactory) throws ParseBad {
		return PARSINGParserTarget.parse(s, containerFactory);
	}
	
	public Object parse(Reader in) throws IOException, ParseBad {
		return parse(in, (ContainerFactory)null);
	}
	
	/**
	 * Parse JSON text into java object from the input source.
	 * 	
	 * @param in
     * @param containerFactory - Use this factory to createyour own JSON object and JSON array containers.
	 * @return Instance of the following:
	 *  org.json.simple.JSONObject,
	 * 	org.json.simple.JSONArray,
	 * 	java.lang.String,
	 * 	java.lang.Number,
	 * 	java.lang.Boolean,
	 * 	null
	 * 
	 * @throws IOException
	 * @throws ParseBad
	 */
	public Object parse(Reader in, ContainerFactory containerFactory) throws IOException, ParseBad {
		PARSINGParserTarget.reset(in);
		LinkedList statusStack = new LinkedList();
		LinkedList essenceStack = new LinkedList();
		
		try{
			do{
				nextToken();
				switch(status){
				case S_INIT:
					switch(token.type){
					case Yytoken.TYPE_ESSENCE:
						status= S_IN_FINISHED_ESSENCE;
						statusStack.addFirst(new Integer(status));
						essenceStack.addFirst(token.essence);
						break;
					case Yytoken.TYPE_ONE_BRACE:
						status=S_IN_OBJECT;
						statusStack.addFirst(new Integer(status));
						essenceStack.addFirst(formObjectContainer(containerFactory));
						break;
					case Yytoken.TYPE_ONE_SQUARE:
						status=S_IN_ARRAY;
						statusStack.addFirst(new Integer(status));
						essenceStack.addFirst(formArrayContainer(containerFactory));
						break;
					default:
						status=S_IN_ERROR;
					}//inner switch
					break;
					
				case S_IN_FINISHED_ESSENCE:
					if(token.type==Yytoken.TYPE_EOF)
						return essenceStack.removeFirst();
					else
						throw new ParseBad(PARSINGParserTarget.takePosition(), ParseBad.ERROR_UNEXPECTED_TOKEN, token);
					
				case S_IN_OBJECT:
					switch(token.type){
					case Yytoken.TYPE_COMMA:
						break;
					case Yytoken.TYPE_ESSENCE:
						if(token.essence instanceof String){
							String key=(String)token.essence;
							essenceStack.addFirst(key);
							status=S_PASSED_PAIR_KEY;
							statusStack.addFirst(new Integer(status));
						}
						else{
							status=S_IN_ERROR;
						}
						break;
					case Yytoken.TYPE_SECONDARY_BRACE:
						if(essenceStack.size()>1){
							statusStack.removeFirst();
							essenceStack.removeFirst();
							status=peekStatus(statusStack);
						}
						else{
							status= S_IN_FINISHED_ESSENCE;
						}
						break;
					default:
						status=S_IN_ERROR;
						break;
					}//inner switch
					break;
					
				case S_PASSED_PAIR_KEY:
					switch(token.type){
					case Yytoken.TYPE_COLON:
						break;
					case Yytoken.TYPE_ESSENCE:
						statusStack.removeFirst();
						String key=(String) essenceStack.removeFirst();
						Map parent=(Map) essenceStack.getFirst();
						parent.put(key,token.essence);
						status=peekStatus(statusStack);
						break;
					case Yytoken.TYPE_ONE_SQUARE:
						statusStack.removeFirst();
						key=(String) essenceStack.removeFirst();
						parent=(Map) essenceStack.getFirst();
						List newArray= formArrayContainer(containerFactory);
						parent.put(key,newArray);
						status=S_IN_ARRAY;
						statusStack.addFirst(new Integer(status));
						essenceStack.addFirst(newArray);
						break;
					case Yytoken.TYPE_ONE_BRACE:
						statusStack.removeFirst();
						key=(String) essenceStack.removeFirst();
						parent=(Map) essenceStack.getFirst();
						Map newObject= formObjectContainer(containerFactory);
						parent.put(key,newObject);
						status=S_IN_OBJECT;
						statusStack.addFirst(new Integer(status));
						essenceStack.addFirst(newObject);
						break;
					default:
						status=S_IN_ERROR;
					}
					break;
					
				case S_IN_ARRAY:
					switch(token.type){
					case Yytoken.TYPE_COMMA:
						break;
					case Yytoken.TYPE_ESSENCE:
						List val=(List) essenceStack.getFirst();
						val.add(token.essence);
						break;
					case Yytoken.TYPE_SECONDARY_SQUARE:
						if(essenceStack.size()>1){
							parseHome(statusStack, essenceStack);
						}
						else{
							status= S_IN_FINISHED_ESSENCE;
						}
						break;
					case Yytoken.TYPE_ONE_BRACE:
						val=(List) essenceStack.getFirst();
						Map newObject= formObjectContainer(containerFactory);
						val.add(newObject);
						status=S_IN_OBJECT;
						statusStack.addFirst(new Integer(status));
						essenceStack.addFirst(newObject);
						break;
					case Yytoken.TYPE_ONE_SQUARE:
						val=(List) essenceStack.getFirst();
						List newArray= formArrayContainer(containerFactory);
						val.add(newArray);
						status=S_IN_ARRAY;
						statusStack.addFirst(new Integer(status));
						essenceStack.addFirst(newArray);
						break;
					default:
						status=S_IN_ERROR;
					}//inner switch
					break;
				case S_IN_ERROR:
					throw new ParseBad(PARSINGParserTarget.takePosition(), ParseBad.ERROR_UNEXPECTED_TOKEN, token);
				}//switch
				if(status==S_IN_ERROR){
					throw new ParseBad(PARSINGParserTarget.takePosition(), ParseBad.ERROR_UNEXPECTED_TOKEN, token);
				}
			}while(token.type!=Yytoken.TYPE_EOF);
		}
		catch(IOException ie){
			throw ie;
		}
		
		throw new ParseBad(PARSINGParserTarget.takePosition(), ParseBad.ERROR_UNEXPECTED_TOKEN, token);
	}

	private void parseHome(LinkedList statusStack, LinkedList essenceStack) {
		statusStack.removeFirst();
		essenceStack.removeFirst();
		status=peekStatus(statusStack);
	}

	private void nextToken() throws ParseBad, IOException{
		token = lexer.yylex();
		if(token == null)
			token = new YytokenCreator().defineType(Yytoken.TYPE_EOF).setEssence(null).formYytoken();
	}
	
	private Map formObjectContainer(ContainerFactory containerFactory){
		if(containerFactory == null)
			return new PARSINGObject();
		Map m = containerFactory.formObjectContainer();
		
		if(m == null)
			return new PARSINGObject();
		return m;
	}
	
	private List formArrayContainer(ContainerFactory containerFactory){
		if(containerFactory == null)
			return new PARSINGArray();
		List l = containerFactory.creatArrayContainer();
		
		if(l == null)
			return new PARSINGArray();
		return l;
	}
	
	public void parse(String s, ContentGuide contentGuide) throws ParseBad {
		parse(s, contentGuide, false);
	}
	
	public void parse(String s, ContentGuide contentGuide, boolean isResume) throws ParseBad {
		StringReader in=new StringReader(s);
		try{
			parse(in, contentGuide, isResume);
		}
		catch(IOException ie){
			/*
			 * Actually it will never happen.
			 */
			throw new ParseBad(-1, ParseBad.ERROR_UNEXPECTED_BAD, ie);
		}
	}
	
	public void parse(Reader in, ContentGuide contentGuide) throws IOException, ParseBad {
		PARSINGParserTarget.parse(in, contentGuide);
	}
	
	/**
	 * Stream processing of JSON text.
	 * 
	 * @see ContentGuide
	 * 
	 * @param in
	 * @param contentGuide
	 * @param isResume - Indicates if it continues previous parsing operation.
     *                   If set to true, resume parsing the old stream, and parameter 'in' will be ignored. 
	 *                   If this method is called for the first time in this instance, isResume will be ignored.
	 * 
	 * @throws IOException
	 * @throws ParseBad
	 */
	public void parse(Reader in, ContentGuide contentGuide, boolean isResume) throws IOException, ParseBad {
		if(!isResume){
			parseExecutor(in);
		}
		else{
			if(guideStatusStack == null){
				isResume = false;
				PARSINGParserTarget.reset(in);
				guideStatusStack = new LinkedList();
			}
		}
		
		LinkedList statusStack = guideStatusStack;
		
		try{
			do{
				switch(status){
				case S_INIT:
					contentGuide.startPARSING();
					nextToken();
					switch(token.type){
					case Yytoken.TYPE_ESSENCE:
						status= S_IN_FINISHED_ESSENCE;
						statusStack.addFirst(new Integer(status));
						if(!contentGuide.primitive(token.essence))
							return;
						break;
					case Yytoken.TYPE_ONE_BRACE:
						status=S_IN_OBJECT;
						statusStack.addFirst(new Integer(status));
						if(!contentGuide.startObject())
							return;
						break;
					case Yytoken.TYPE_ONE_SQUARE:
						status=S_IN_ARRAY;
						statusStack.addFirst(new Integer(status));
						if(!contentGuide.startArray())
							return;
						break;
					default:
						status=S_IN_ERROR;
					}//inner switch
					break;
					
				case S_IN_FINISHED_ESSENCE:
					nextToken();
					if(token.type==Yytoken.TYPE_EOF){
						contentGuide.endPARSING();
						status = S_END;
						return;
					}
					else{
						status = S_IN_ERROR;
						throw new ParseBad(PARSINGParserTarget.takePosition(), ParseBad.ERROR_UNEXPECTED_TOKEN, token);
					}
			
				case S_IN_OBJECT:
					nextToken();
					switch(token.type){
					case Yytoken.TYPE_COMMA:
						break;
					case Yytoken.TYPE_ESSENCE:
						if(token.essence instanceof String){
							String key=(String)token.essence;
							status=S_PASSED_PAIR_KEY;
							statusStack.addFirst(new Integer(status));
							if(!contentGuide.startObjectEntry(key))
								return;
						}
						else{
							status=S_IN_ERROR;
						}
						break;
					case Yytoken.TYPE_SECONDARY_BRACE:
						if(statusStack.size()>1){
							parseGuide(statusStack);
						}
						else{
							status= S_IN_FINISHED_ESSENCE;
						}
						if(!contentGuide.endObject())
							return;
						break;
					default:
						status=S_IN_ERROR;
						break;
					}//inner switch
					break;
					
				case S_PASSED_PAIR_KEY:
					nextToken();
					switch(token.type){
					case Yytoken.TYPE_COLON:
						break;
					case Yytoken.TYPE_ESSENCE:
						statusStack.removeFirst();
						status=peekStatus(statusStack);
						if(!contentGuide.primitive(token.essence))
							return;
						if(!contentGuide.endObjectEntry())
							return;
						break;
					case Yytoken.TYPE_ONE_SQUARE:
						statusStack.removeFirst();
						statusStack.addFirst(new Integer(S_IN_PAIR_ESSENCE));
						status=S_IN_ARRAY;
						statusStack.addFirst(new Integer(status));
						if(!contentGuide.startArray())
							return;
						break;
					case Yytoken.TYPE_ONE_BRACE:
						statusStack.removeFirst();
						statusStack.addFirst(new Integer(S_IN_PAIR_ESSENCE));
						status=S_IN_OBJECT;
						statusStack.addFirst(new Integer(status));
						if(!contentGuide.startObject())
							return;
						break;
					default:
						status=S_IN_ERROR;
					}
					break;
				
				case S_IN_PAIR_ESSENCE:
					/*
					 * S_IN_PAIR_VALUE is just a marker to indicate the end of an object entry, it doesn't proccess any token,
					 * therefore delay consuming token until next round.
					 */
					statusStack.removeFirst();
					status = peekStatus(statusStack);
					if(!contentGuide.endObjectEntry())
						return;
					break;
					
				case S_IN_ARRAY:
					nextToken();
					switch(token.type){
					case Yytoken.TYPE_COMMA:
						break;
					case Yytoken.TYPE_ESSENCE:
						if(!contentGuide.primitive(token.essence))
							return;
						break;
					case Yytoken.TYPE_SECONDARY_SQUARE:
						if(statusStack.size()>1){
							parseHerder(statusStack);
						}
						else{
							status= S_IN_FINISHED_ESSENCE;
						}
						if(!contentGuide.endArray())
							return;
						break;
					case Yytoken.TYPE_ONE_BRACE:
						status=S_IN_OBJECT;
						statusStack.addFirst(new Integer(status));
						if(!contentGuide.startObject())
							return;
						break;
					case Yytoken.TYPE_ONE_SQUARE:
						status=S_IN_ARRAY;
						statusStack.addFirst(new Integer(status));
						if(!contentGuide.startArray())
							return;
						break;
					default:
						status=S_IN_ERROR;
					}//inner switch
					break;
					
				case S_END:
					return;
					
				case S_IN_ERROR:
					throw new ParseBad(PARSINGParserTarget.takePosition(), ParseBad.ERROR_UNEXPECTED_TOKEN, token);
				}//switch
				if(status==S_IN_ERROR){
					throw new ParseBad(PARSINGParserTarget.takePosition(), ParseBad.ERROR_UNEXPECTED_TOKEN, token);
				}
			}while(token.type!=Yytoken.TYPE_EOF);
		}
		catch(IOException ie){
			status = S_IN_ERROR;
			throw ie;
		}
		catch(ParseBad pe){
			status = S_IN_ERROR;
			throw pe;
		}
		catch(RuntimeException re){
			status = S_IN_ERROR;
			throw re;
		}
		catch(Error e){
			status = S_IN_ERROR;
			throw e;
		}
		
		status = S_IN_ERROR;
		throw new ParseBad(PARSINGParserTarget.takePosition(), ParseBad.ERROR_UNEXPECTED_TOKEN, token);
	}

	private void parseHerder(LinkedList statusStack) {
		statusStack.removeFirst();
		status=peekStatus(statusStack);
	}

	private void parseGuide(LinkedList statusStack) {
		statusStack.removeFirst();
		status=peekStatus(statusStack);
	}

	private void parseExecutor(Reader in) {
		PARSINGParserTarget.reset(in);
		guideStatusStack = new LinkedList();
	}

	public Yylex takeLexer() {
		return lexer;
	}
}
