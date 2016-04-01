import java.io.BufferedReader;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.PrintWriter;
import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class inference{

	public static void main(String args[]) throws FileNotFoundException{
		// printer to print to output file
		PrintWriter printer = new PrintWriter("output.txt");
		try
		{
			//file from where input is fetched
			String fileName = "input.txt";
			
		    backwardChainingAlorithm(fileName,printer);
			
		    printer.close();
		}
		catch(Exception e)
		{
			printer.println("FALSE");
			
		}
	}

	// method to implement backward chaining algorithm
	public static void backwardChainingAlorithm(String inputFileName,PrintWriter printer) throws FileNotFoundException
	{
		//setting scanner object to scan the input
		Scanner sc = new Scanner(new BufferedReader(new FileReader(inputFileName)));

		//read queries from input file
		int numOfQueries = Integer.parseInt(sc.nextLine());
	    
		//Get the queries from the input
		List<predicate> queries = GetQueries(numOfQueries, sc);	
		
		//read knowledge base from input file
		int kbSize = Integer.parseInt(sc.nextLine());
		knowledgeBase kb = new knowledgeBase();	
		UpdateKnowledgeBase(kb,kbSize,sc);
		sc.close();

		//parse for each query in knowledge base
		for(int count = 0;count< queries.size(); count ++)
		{
			try{
				LinkedHashMap<variable,argument> theta = new LinkedHashMap<variable,argument>();
				List<predicate> exitCondition = new ArrayList<predicate>();
				predicate currentQuery = queries.get(count);

				//Calling backward chaining one by one for all the queries
				List<Map<variable, argument>> variables = 
						backwardChainingOr(kb,currentQuery, theta, exitCondition);
				
				//checking if the subsitution list is empty=> means the query can't be proven from the KB
				if(variables.isEmpty())
				{
					if(printer != null)
						printer.println("FALSE");
				}
				else
				{
					if(printer != null)
						printer.println("TRUE");
				}	}

			catch(Exception e)
			{
				printer.println("FALSE");
			}
		}
		
	}

	private static List<Map<variable, argument>> backwardChainingOr(
			knowledgeBase kb, predicate currentQuery,
			Map<variable, argument> theta,
			List<predicate> exitCondition) 
			{
		// TODO Auto-generated method stub

		List<Map<variable, argument>> substitutionLst = new ArrayList<Map<variable, argument>>();

		predicate goal =  currentQuery;
		
		//getting predicate copy from the goal
		predicate predicateCopy = GetPredicateCopy(goal,theta);
		
		if (!exitCondition.contains(predicateCopy))
			exitCondition.add(predicateCopy);
		else
			return null;
		
		for (Integer key : kb.conclusions.keySet()) {
			predicate p = kb.conclusions.get(key);

			if (p.GetPredicateName().equals(goal.GetPredicateName())
					&& (p.IsNegated() == goal.IsNegated())) {
				
				
				List<Map<variable, argument>> tempsubstitutionList = new ArrayList<Map<variable, argument>>();
				Map<variable, argument> thetatemp = new LinkedHashMap<>();

				thetatemp.putAll(theta);

				List<predicate> predicates = null;
				for (Integer keyvalue : kb.assumptionMap.keySet()) {
					if (keyvalue == key) {

						predicates = kb.assumptionMap.get(keyvalue);
					}
				}								

				Map<variable, argument> thetaDelta = unify(p, predicateCopy, thetatemp);

				if (thetaDelta != null) {	

					if(predicates != null)
					{
						tempsubstitutionList = backwardChainingForList(kb, predicates, thetaDelta,
								exitCondition,true,1);
					}

					if (!tempsubstitutionList.isEmpty())
						substitutionLst.addAll(tempsubstitutionList);
				}

			}

		}
		
		return substitutionLst;	

			}
	


	private static Wrapper StandardizeVariable(predicate p,
			Map<variable, argument> theta,List<predicate> predicates ) {
		// TODO Auto-generated method stub

		boolean retVal = true;

		Wrapper wrap = new Wrapper();

		for(argument arg : p.GetTerms())
		{
			if(arg instanceof variable)
				retVal = false;
		}	

		if(retVal)
		{
			wrap.predi = p;
			wrap.tempDel = theta;

			return wrap;
		}

		predicate predicateCopy = GetPredicateCopy(p, theta);

		for(int i = 0 ; i< predicateCopy.GetTerms().size(); i++)
		{
			argument arg = predicateCopy.arguments.get(i);
			if(arg instanceof constant)
				continue;
			else
			{
				variable val = (variable)arg;
				variable var = val;
				if(theta.containsKey(val))
				{
					boolean unique = false;
					while(!unique)
					{
						String name =  val.GetValue() + "1";
						var = new variable(name);

						unique = theta.containsKey(var);


					}

					int index = predicateCopy.arguments.indexOf(arg);
					predicateCopy.arguments.remove(arg);
					predicateCopy.arguments.add(index, var);
				}
			}
		}

		List<predicate> copyPredicates = new ArrayList<predicate>();
		for(predicate pre : predicates)
		{
			predicate cop = GetPredicateCopy(pre, theta);
			copyPredicates.add(cop);
		}
		for(predicate pre : copyPredicates)
		{
			for(int i = 0 ; i< pre.GetTerms().size(); i++)
			{
				argument arg = pre.arguments.get(i);
				if(arg instanceof constant)
					continue;
				else
				{
					variable val = (variable)arg;
					variable var = val;
					if(theta.containsKey(val))
					{
						boolean unique = false;
						while(!unique)
						{
							String name =  val.GetValue() + "1";
							var = new variable(name);

							unique = theta.containsKey(var);


						}

						//change
						int index = pre.arguments.indexOf(arg);
						pre.arguments.remove(arg);
						pre.arguments.add(index, var);
					}
				}
			}
		}

		wrap.predi = predicateCopy;
		wrap.predicates = copyPredicates;

		return wrap;


	}


	private static List<Map<variable, argument>> backwardChainingForList(knowledgeBase kb,
			List<predicate> predicatList, Map<variable, argument> thetaDelta,
			List<predicate> exitCondition,boolean isTrue,int num) {
		// TODO Auto-generated method stub
		List<Map<variable, argument>> substitutionList = new ArrayList<Map<variable, argument>>();

		if (thetaDelta == null)
			return null;

		else if (predicatList.isEmpty()) {
			substitutionList.add(thetaDelta);
			return substitutionList;
		} else {			

			predicate first = predicatList.get(0);

			predicate predicateCopy = GetPredicateCopy(first, thetaDelta);

			Wrapper wrapper = SubstituteThetaInQuery(predicateCopy,thetaDelta,true);

			predicateCopy = wrapper.predi;

			if (exitCondition == null || exitCondition.isEmpty() || exitCondition.contains(predicateCopy)) {
				return substitutionList;
			}


			List<predicate> goalarry = new ArrayList<>();
			goalarry.addAll(exitCondition);


			List<predicate> rest = predicatList.subList(1, predicatList.size());

			Map<variable, argument> thetaDel3 = TrimCharac(thetaDelta,predicateCopy.sentenceNumber,1,new Wrapper());


			List<Map<variable, argument>> substitutionList1 = backwardChainingOr
					(kb, predicateCopy, thetaDel3,
							goalarry);					

			if(substitutionList1 != null)
			{
				for (Map<variable, argument> theta1 : substitutionList1) 
				{
					theta1.putAll(thetaDelta);
				}
			}


			if(substitutionList1 != null){								
				for (Map<variable, argument> theta1 : substitutionList1)
				{			
					List<Map<variable, argument>> substitutionList12 = backwardChainingForList(kb, rest, theta1, exitCondition,true,1);
					if (!substitutionList12.isEmpty()) {

						substitutionList.addAll(substitutionList12);

					}
				}
			}

		}
		return substitutionList;

	}

	private static Wrapper SubstituteThetaInQuery(
			predicate query, Map<variable, argument> thetaDelta,boolean toSubstitue) {
		// TODO Auto-generated method stub
		List<argument> arguments = query.GetTerms();
		List<argument> tempArguments = new ArrayList<argument>();
		for (int i = 0; i < arguments.size(); i++) {
			argument currentArg = arguments.get(i);

			argument argumentToAdd = null;

			if(currentArg instanceof constant){
				argumentToAdd = currentArg;
			}
			else
			{
				argumentToAdd = new variable(currentArg.GetValue());
				// index to copy
			}
			tempArguments.add(argumentToAdd);
		}
		Map<variable, argument> tempDel = new HashMap<variable, argument>(); 
		for(argument arg :tempArguments){
			for(variable key : thetaDelta.keySet())
			{
				if(key.equals(arg)&& thetaDelta.get(key) instanceof constant)
				{
					int index = query.arguments.indexOf(arg);
					query.arguments.remove(index);
					query.arguments.add(index, thetaDelta.get(key));
				}
			}
		}

		Wrapper classWrapper = new Wrapper();
		classWrapper.predi = query;
		classWrapper.tempDel = tempDel;

		return classWrapper;
	}


	private static Map<variable, argument> TrimCharac(
			Map<variable, argument> thetaDelta, int sentenceNumber,int toTrim12,Wrapper wrap123) {
		// TODO Auto-generated method stub
		Map<variable, argument> tempDel = new HashMap<variable, argument>();
		for(variable key : thetaDelta.keySet()){
			String strin = key.GetValue().substring(1);
			if(Integer.parseInt(strin) == sentenceNumber)
			{
				if(thetaDelta.get(key) instanceof constant)
				{
					tempDel.put(key, thetaDelta.get(key));
				}
				else
					if(thetaDelta.get(key) instanceof variable)
					{
						variable variableKey = key;
						while(thetaDelta.get(variableKey) instanceof variable)
						{
							argument val = thetaDelta.get(variableKey);
							argument val1 = thetaDelta.get(val);

							if(val1 == null)
							{
								tempDel.put(key, val);
								break;
							}

							if(val1 != null && val1 instanceof constant)
							{
								tempDel.put(key, val1);
								break;
							}
							else
								if (val1 != null && val1 instanceof variable)
									variableKey = (variable) val;

						}
					}

			}
		}
		return tempDel;
	}


	// method to unify nodes
	private static Map<variable, argument> unify(Node x,
			Node y, Map<variable, argument> thetatemp) {
		// TODO Auto-generated method stub
		if (thetatemp == null) {
			return null;
		} else if (x.equals(y)) {

			return thetatemp;
		} else if (x instanceof variable) {

			return unifyVariables((variable) x, y, thetatemp);
		} else if (y instanceof variable) {

			return unifyVariables((variable) y, x, thetatemp);
		} else if (isCompound(x) && isCompound(y)) {

			return unify(FindArguments(x), FindArguments(y), unifyOperators(FindOperator(x), FindOperator(y), thetatemp));
		} 
		else
			return null;

	}

	public static Map<variable, argument> unify(List<? extends Node> x, List<? extends Node> y, Map<variable, argument> theta) {
		if (theta == null) {
			return null;
		} else if (x.size() != y.size()) {
			return null;
		} else if (x.size() == 0 && y.size() == 0) {
			return theta;
		} else if (x.size() == 1 && y.size() == 1) {
			return unify(x.get(0), y.get(0), theta);
		} else {
			return unify(x.subList(1, x.size()), y.subList(1, y.size()), unify(x.get(0), y.get(0), theta));
		}
	}

	private static boolean IsEquality(Node x, Node y) {
		// TODO Auto-generated method stub

		if(x instanceof predicate && y instanceof predicate)
		{
			return IsPredicateEqual((predicate)x,(predicate)y);
		}
		else
			if(x instanceof constant && y instanceof constant)
			{
				return IsConstantEqual((constant)x,(constant)y);
			}
			else
				if(x instanceof variable && y instanceof variable)
				{
					return IsVariablesEqual((variable)x,(variable)y);
				}

		return false;
	}

	private static boolean IsVariablesEqual(variable x, variable y) {
		// TODO Auto-generated method stub
		return x.GetValue().equals(y.GetValue());
	}

	private static boolean IsConstantEqual(constant x, constant y) {
		// TODO Auto-generated method stub
		return x.GetValue().equals(x.GetValue());
	}

	private static boolean IsPredicateEqual(predicate x, predicate y) {
		// TODO Auto-generated method stub
		return x.GetPredicateName().equals(y.GetPredicateName()) 
				&& x.IsNegated() == y.IsNegated()
				&& IsTwoArgumentListSame(x.GetTerms(),y.GetTerms());
	}

	private static boolean IsTwoArgumentListSame(List<argument> arguments1,
			List<argument> arguments2) {
		// TODO Auto-generated method stub

		if(arguments1 == null && arguments2 == null)
			return true;

		if(arguments1 == null || arguments2 == null)
			return false;

		if(arguments1.size() != arguments2.size())
			return false;

		boolean isEqual = true;
		for(int count = 0; count< arguments1.size(); count++){

			argument x = arguments1.get(count);
			argument y = arguments2.get(count);

			if(x instanceof variable && y instanceof variable)
			{
				isEqual = IsVariablesEqual((variable)x,(variable)y);
			}
			else 
				if(x instanceof constant && y instanceof constant)
				{
					isEqual = IsConstantEqual((constant)x, (constant)y);
				}
				else
				{
					isEqual = false;
				}
			if(!isEqual)
				break;

		}

		return isEqual;
	}

	private static boolean isCompound(Node x) {
		// TODO Auto-generated method stub
		return x instanceof predicate;			
	}

	private static Map<variable, argument> unifyOperators(String x, String y,
			Map<variable, argument> thetatemp) {
		if (thetatemp == null) 
		{
			return null;
		} else if (x.equals(y)) 
		{
			return thetatemp;
		} else 
		{
			return null;
		}
	}

	private static String FindOperator(Node x) {
		// TODO Auto-generated method stub

		String returnValue = "";
		if (x == null)
			return null;
		if(x instanceof variable)
			returnValue = ((variable)x).GetValue();
		else
			if(x instanceof constant)
				returnValue = ((constant)x).GetValue();
			else
				if(x instanceof predicate)
					returnValue = ((predicate)x).GetPredicateName();


		return returnValue;
	}

	private static List<argument> FindArguments(Node x) {
		// TODO Auto-generated method stub
		if(x != null && x instanceof predicate)
		{
			predicate tempPredicate = (predicate)x;
			return tempPredicate.GetTerms();
		}
		return null;
	}

	private static Map<variable, argument> unifyVariables(variable var, Node x,
			Map<variable, argument> thetatemp) {
		// TODO Auto-generated method stub
		if (!argument.class.isInstance(x)) {
			return null;
		} else if (thetatemp.keySet().contains(var)) {
			return unify(thetatemp.get(var), x, thetatemp);
		} else if (thetatemp.keySet().contains(x)) {

			return unify(var, thetatemp.get(x), thetatemp);
		} 
		else {
			thetatemp.put(var,(argument) x);
			return thetatemp;
		}
	}

	//method to copy the predicate from one object to another
	private static predicate GetPredicateCopy(predicate goal,
			Map<variable, argument> theta) {
		// TODO Auto-generated method stub
		List<argument> arguments = goal.GetTerms();
		List<argument> tempArguments = new ArrayList<argument>();
		for (int i = 0; i < arguments.size(); i++) {
			argument currentArg = arguments.get(i);

			argument argumentToAdd = null;

			if(currentArg instanceof constant){
				argumentToAdd = currentArg;
			}
			else
			{
				argumentToAdd = new variable(currentArg.GetValue());
				// index to copy
			}
			tempArguments.add(argumentToAdd);
		}
		predicate newPredicate =  new predicate(goal.GetPredicateName(), tempArguments);

		newPredicate.SetIsNegated(goal.IsNegated());

		newPredicate.sentenceNumber = goal.sentenceNumber;

		return newPredicate;
	}

	//Method to get predicates sentences 
	public static List<predicate> GetQueries(int counter, Scanner sc) {
		// TODO Auto-generated method stub
		List<predicate> sentences = new ArrayList<predicate>();	
		predicate sentence = null;
		for(int count = 0; count < counter ; count ++)
		{
			//String clause = sc.nextLine();
			String clause = sc.nextLine();
			// if(clause != null && !clause.isEmpty()){
			sentence = GetPredicate(clause,count+1);
			sentences.add(sentence);
			//}
		}
		return sentences;
	}

	// method to convert string to predicate
	public static predicate GetPredicate(String sentence,int predicateSequence) {
		String predicateName = GetPredicateName(sentence);
		List<argument> arguments = ExtractTermsFromSentence(sentence,predicateSequence);	    
		predicate tempPredicate = new predicate(predicateName,arguments);	    
		SetIsNegatedFieldOfPredicate(tempPredicate,sentence);
		return tempPredicate;
	}

	//method to check and set negative property for predicate
	private static void SetIsNegatedFieldOfPredicate(predicate tempPredicate,String sentence) {
		// TODO Auto-generated method stub
		String negatedSign = "~";
		tempPredicate.SetIsNegated(false);
		if(sentence.contains(negatedSign)){
			tempPredicate.SetIsNegated(true);
		}
	}

	//method to extract arguments from string
	public static String GetArgumentFromSentence(String sentence){
		String regexForArguments = "\\(([^)]+)\\)";

		Matcher m = Pattern.compile(regexForArguments).matcher(sentence);
		String arguments=null;
		while(m.find()) {
			//System.out.println(m.group(1));  
			arguments=m.group(1);
		}
		return arguments;
	}
	//method to split string on basis of comma
	public static List<argument> SplitArguments(String query,int predicateSequence)
	{
		String comma = ",";
		List<argument> argumentList=new ArrayList<>();
		String[] argumentArray = query.split(comma);
		if(argumentArray != null)
		{
			for(int i=0;i<argumentArray.length;i++){ 
				if(argumentArray[i].length()==1 && utility.isLowerCaseCharater(argumentArray[i].charAt(0))){
					variable var=new variable(argumentArray[i]+predicateSequence);
					argumentList.add(var);
				}
				else{
					constant c=new constant(argumentArray[i]);
					argumentList.add(c);
				}
			}
		}
		return argumentList;
	}

	//method to extract content within braces
	public static List<argument> ExtractTermsFromSentence(String sentence,int predicateSequence) {

		String arguments = GetArgumentFromSentence(sentence);
		List<argument> lstArgs = SplitArguments(arguments,predicateSequence);
		return lstArgs;
	}

	//method to extract Name before comma
	// Method to return the predicate name from the sentence
	public static String GetPredicateName(String sentence) {

		String tempSentence = null;
		Pattern pattern = null;
		String regexForNegatedQuery = "~(.*?)\\(";
		String regexForPositiveQuery = "(.*?)\\(";
		String negatedSign = "~";
		//to check negated sentence
		if(sentence.contains(negatedSign)){
			pattern = Pattern.compile(regexForNegatedQuery);
		}
		else{
			//to check non-negated sentence
			pattern = Pattern.compile(regexForPositiveQuery);		
		}
		//to match with sentence
		Matcher matcher = pattern.matcher(sentence);
		//to find pattern
		if (matcher.find()) {
			tempSentence=matcher.group(1);
		}				
		return tempSentence;
	}

	// method to update knowledge base
	public static void UpdateKnowledgeBase(knowledgeBase kb, int kbSize2,Scanner sc) {

		String implicationSign = "=>";
		String andSing = "\\^";

		kb.conclusions = new HashMap<Integer, predicate>();
		kb.assumptionMap = new HashMap<Integer, List<predicate>>();

		for(int count = 0; count < kbSize2 ; count ++)
		{
			String nextLine = sc.nextLine();
			List<predicate> predicates = new ArrayList<predicate>();
			if(nextLine.contains(implicationSign))
			{		 
				String[] assumptionAndCon = nextLine.split(implicationSign);

				//add premises
				String[] assumptions = assumptionAndCon[0].split(andSing);				
				AddPremisesToPreicates(assumptions,predicates,count+1);

				//add conclusion
				String extractedConc = assumptionAndCon[1].trim();
				AddConclusion(extractedConc,kb.conclusions,count+1);		   

			}
			else
			{
				//it is fact - add only to conclusion
				AddConclusion(nextLine,kb.conclusions,count+1);
			}

			kb.assumptionMap.put(count+1, predicates);
		}
	}

	//Method to add assumptions on list in predicates
	private static void AddPremisesToPreicates(String[] assumptions,
			List<predicate> predicates, int predicateSequenceNumber) {
		for(int conjuctIndex = 0 ; conjuctIndex < assumptions.length ; conjuctIndex++){				   
			String extractedPredicate = assumptions[conjuctIndex].trim();
			predicate tempPredicate = GetPredicate(extractedPredicate,predicateSequenceNumber);
			tempPredicate.sentenceNumber = predicateSequenceNumber;
			predicates.add(tempPredicate);
		}
	}

	//method to add conclusion to HashMap of conclusions
	private static void AddConclusion(String conclusion,
			HashMap<Integer, predicate> conclusions, int conclusionSequence) {

		predicate tempConclusion = GetPredicate(conclusion,conclusionSequence);
		conclusions.put(conclusionSequence,tempConclusion);
	}

}

//interface to form a tree
interface Node{

}

//interface to represent argument in the predicate/fact/conclusion
interface argument extends Node{
	public String GetValue();

}

//class to represent when argument is variable
class variable implements argument
{
	public String varValue;
	private int hashCode = 0;

	public variable(String variableVal)
	{
		varValue = variableVal;
	}
	public String GetValue(){
		return varValue;
	}

	@Override
	public boolean equals(Object arg0) 
	{
		// TODO Auto-generated method stub

		if(!(arg0 instanceof variable))
			return false;

		variable temp = (variable) arg0;

		return this.GetValue().equals(temp.GetValue());
	}


	@Override
	public int hashCode() {
		// TODO Auto-generated method stub
		if(0 == hashCode)
		{
			hashCode = 5;
			hashCode = 23 * hashCode + varValue.hashCode();
		}

		return hashCode;
	}
}
//class to represent when argument is constant
class constant implements argument{	
	private String constValue;
	private int hashCode = 0;
	public constant(String constVal){
		constValue = constVal;
	}

	public String GetValue(){
		return constValue;
	}


	@Override
	public boolean equals(Object arg0) {
		// TODO Auto-generated method stub
		if(!(arg0 instanceof constant))
			return false;

		constant temp = (constant) arg0;

		return this.GetValue().equals(temp.GetValue());
	}

	@Override
	public int hashCode() {
		// TODO Auto-generated method stub
		if(0 == hashCode)
		{
			hashCode = 5;
			hashCode = 23 * hashCode + constValue.hashCode();
		}

		return hashCode;
	}
}

//class to represent predicate
class predicate implements Node{

	private String name;
	public List<argument> arguments;
	private boolean isNegated = false;
	String stringRep = null;
	int sentenceNumber = 0;

	public predicate(String predicateName, List<argument> argumentLst){
		name = predicateName;
		arguments = argumentLst;
	}

	public boolean IsVisited = false;
	public String GetPredicateName() {
		return name;
	}
	public List<argument> GetTerms() {
		return arguments;
	}

	public boolean IsNegated() {
		return isNegated;
	}

	public void SetIsNegated(boolean isNegated) {
		this.isNegated = isNegated;
	}

	@Override
	public boolean equals(Object arg0) 
	{
		// TODO Auto-generated method stub

		if(!(arg0 instanceof predicate))
			return false;

		predicate tempPredicate = (predicate) arg0;
		return this.GetPredicateName().equals(tempPredicate.GetPredicateName()) 
				&& this.IsNegated() == tempPredicate.IsNegated()
				&& this.GetTerms().equals(tempPredicate.GetTerms());
	}
}

//Class to represent KB which contains premises and conclusion
class knowledgeBase{
	public HashMap<Integer, List<predicate>> assumptionMap = new HashMap<>();
	public HashMap<Integer, predicate> conclusions = new HashMap<Integer, predicate>();
}

//class to define common utility  functionality
class utility{

	static boolean isUpperCaseCharacter(char character) {

		boolean isUpperCase = character >= 'A' && character <= 'Z';
		return isUpperCase;
	}
	
	static boolean isLowerCaseCharater(char character) {

		boolean isLowerCase = character >= 'a' && character <= 'z';
		return isLowerCase;
	}
}

//wrapper class to pass values in between the functions
class Wrapper
{
	public predicate predi;
	public Map<variable, argument> tempDel;
	public List<predicate> predicates;
}
