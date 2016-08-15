package neural;

import java.util.ArrayList;

import fileReader.FileReader;

public class Network {
	private ArrayList<Neuron> inputLayer, outputLayer;
	private int inputSize, outputSize, hiddenLayersNumber;
	private ArrayList<Integer> hiddenSizes;
	private ArrayList<ArrayList<Neuron>> hiddenLayers;
	private double learningRate;
	String filename;

	public Network(int inputNumber,int outputNumber, double learningRate , int hiddenLayersNumber, String filename) {
		// TODO Auto-generated constructor stub
	
		inputSize = inputNumber;
		outputSize = outputNumber;
		this.hiddenLayersNumber = hiddenLayersNumber;
		this.learningRate = learningRate;
		this.filename = filename;

		inputLayer = new ArrayList<Neuron>();
		hiddenLayers = new ArrayList<ArrayList<Neuron>>();
		outputLayer = new ArrayList<Neuron>();
		hiddenSizes = new ArrayList<Integer>();

		for(int i = 0; i < inputSize; i++)
		{
			inputLayer.add(new Neuron((inputNumber + outputNumber)/2));//tamanho da primeira camada escondida
		}


		for(int i = 0; i < hiddenLayersNumber; i++)
		{
			int neuronsSize;
			ArrayList<Neuron> tempLayer = new ArrayList<Neuron>();
			if(i == 0)
				neuronsSize = (inputNumber + outputNumber)/2;
			else
				neuronsSize = (hiddenSizes.listIterator(i-1).next() + outputNumber)/2;
			hiddenSizes.add(neuronsSize);
			for(int j = 0; j < neuronsSize; j++)
			{
				tempLayer.add(new Neuron((neuronsSize + outputNumber)/2));
			}
			hiddenLayers.add(tempLayer);
		}

		for(int i = 0; i < outputSize; i++)
		{
			outputLayer.add(new Neuron(0));
		}
	}


	private void normalizeValues(ArrayList<Neuron> layer)
	{

		for(int j = 0; j < layer.size();j++)
		{
			double normalize = sigmoide(layer.listIterator(j).next().getValue() + layer.listIterator(j).next().getBias());
			layer.listIterator(j).next().setValue(normalize);
		}

	}


	private void hiddenFrontPropagation()
	{
		for(int i = 0; i < hiddenLayersNumber -1;i++)//at� � pen�ltima camada
		{

			for(int j = 0; j < hiddenSizes.listIterator(i).next();j++)
			{
				for(int k = 0; k < hiddenSizes.listIterator(i+1).next(); k++)
				{
					
					double netValue = hiddenLayers.listIterator(i).next().listIterator(j).next().getWeights().listIterator(k).next() * hiddenLayers.listIterator(i).next().listIterator(j).next().getValue();
					
					hiddenLayers.listIterator(i+1).next().listIterator(k).next().addValue(netValue);

				}

				normalizeValues(hiddenLayers.listIterator(i+1).next());
			}

		}
	}

	public void frontPropagation(double inputValues[])
	{
		for(int i = 0; i < inputValues.length;i++)
		{
			inputLayer.listIterator(i).next().setValue(sigmoide(inputValues[i]));		
			for(int j = 0; j < hiddenSizes.listIterator(0).next();j++)
			{	
				double netValue = inputLayer.listIterator(i).next().getWeights().listIterator(j).next() * inputLayer.listIterator(i).next().getValue();
				hiddenLayers.listIterator(0).next().listIterator(j).next().addValue(netValue);//primeira camada
			}
		}

		normalizeValues(hiddenLayers.listIterator(0).next());

		hiddenFrontPropagation();

		for(int i = 0; i < hiddenSizes.listIterator(hiddenLayersNumber-1).next();i++)
		{
			for(int j = 0; j < outputSize;j++)
			{
				double netValue =  hiddenLayers.listIterator(hiddenLayersNumber-1).next().listIterator(i).next().getWeights().listIterator(j).next() * inputLayer.listIterator(i).next().getValue();
				netValue +=  hiddenLayers.listIterator(hiddenLayersNumber-1).next().listIterator(i).next().getBias();

				
					outputLayer.listIterator(j).next().addValue(netValue);
			}
		}

		normalizeValues(outputLayer);
	}

	public void backPropagation(double ExpectedOutputValues[]){
		updateDeltas(ExpectedOutputValues);
		updateWeightBias();
	}

	private void updateHiddenDeltas()
	{
		for(int i = hiddenLayersNumber -2; i > -1; i--)
		{
			for(int j = 0; j < hiddenSizes.listIterator(i).next();j++)
			{
				for(int k = 0; k < hiddenSizes.listIterator(i+1).next();k++)
				{
					hiddenLayers.listIterator(i).next().listIterator(j).next().addErrorFactor(hiddenLayers.listIterator(i+1).next().listIterator(k).next().getDelta() * hiddenLayers.listIterator(i).next().listIterator(k).next().getWeights().listIterator(j).next());  
				}
				hiddenLayers.listIterator(i).next().listIterator(j).next().setDelta(hiddenLayers.listIterator(i).next().listIterator(j).next().getValue() * (1 - hiddenLayers.listIterator(i).next().listIterator(j).next().getValue()) * hiddenLayers.listIterator(i).next().listIterator(j).next().getErrorFactor());
			}
		}
	}

	private void updateDeltas(double ExpectedOutputValues[]){

		for(int i = 0 ; i < outputSize; i++){
			outputLayer.listIterator(i).next().setErrorFactor(ExpectedOutputValues[i] - outputLayer.listIterator(i).next().getValue());	
			double newDelta = outputLayer.listIterator(i).next().getValue() * (1.0 - outputLayer.listIterator(i).next().getValue()) * outputLayer.listIterator(i).next().getErrorFactor();
			outputLayer.listIterator(i).next().setDelta(newDelta);
		}


		////Last hidden Layer
		for( int i = 0 ; i < hiddenSizes.listIterator(hiddenLayersNumber -1).next(); i++)
		{
			for (int j=0 ; j < outputSize;j++)
				hiddenLayers.listIterator(hiddenLayersNumber -1).next().listIterator(i).next().addErrorFactor(outputLayer.listIterator(j).next().getDelta() * hiddenLayers.listIterator(hiddenLayersNumber -1).next().listIterator(i).next().getWeights().listIterator(j).next());			
			hiddenLayers.listIterator(hiddenLayersNumber -1).next().listIterator(i).next().setDelta(hiddenLayers.listIterator(hiddenLayersNumber -1).next().listIterator(i).next().getValue() * (1 - hiddenLayers.listIterator(hiddenLayersNumber -1).next().listIterator(i).next().getValue()) * hiddenLayers.listIterator(hiddenLayersNumber -1).next().listIterator(i).next().getErrorFactor());
		}

		updateHiddenDeltas();

	}


	private void updateHiddenWeightBias()
	{
		//�ltima camada
		for(int i = 0; i < hiddenSizes.listIterator(hiddenLayersNumber-1).next(); i++)
		{
			for(int j = 0; j < outputSize; j++)
			{
				hiddenLayers.listIterator(hiddenLayersNumber -1).next().listIterator(i).next().getWeights().set(j, hiddenLayers.listIterator(hiddenLayersNumber -1).next().listIterator(i).next().getWeights().listIterator(j).next() +
						learningRate * 	outputLayer.listIterator(j).next().getValue()*outputLayer.listIterator(j).next().getDelta());
			}

			hiddenLayers.listIterator(hiddenLayersNumber -1).next().listIterator(i).next().updateBias(learningRate);
		}



		for(int i = hiddenLayersNumber-3; i >-1 ; i--)
		{
			for(int j = 0; j < hiddenSizes.listIterator(i).next();j++)
			{
				for(int k = 0;k < hiddenSizes.listIterator(i+1).next();k++)
				{
					hiddenLayers.listIterator(i).next().listIterator(i).next().getWeights().set(j, hiddenLayers.listIterator(i).next().listIterator(i).next().getWeights().listIterator(j).next() -
							learningRate * 	hiddenLayers.listIterator(i+1).next().listIterator(j).next().getValue()*hiddenLayers.listIterator(i+1).next().listIterator(j).next().getDelta());

				}
				hiddenLayers.listIterator(i).next().listIterator(i).next().updateBias(learningRate);

			}



		}

	}

	private void updateWeightBias()
	{

		for(int i = 0; i < outputSize; i++)
		{
			outputLayer.listIterator(i).next().updateBias(learningRate);
		}

		updateHiddenWeightBias();


		for(int i = 0; i < inputSize; i++)
		{	
			for(int j = 0; j < hiddenSizes.listIterator(0).next(); j++)
			{
				double temp= inputLayer.listIterator(i).next().getWeights().listIterator(j).next() -
						learningRate * 	hiddenLayers.listIterator(0).next().listIterator(j).next().getValue()*hiddenLayers.listIterator(0).next().listIterator(j).next().getDelta();

				inputLayer.listIterator(i).next().getWeights().set(j, temp);
			}

			inputLayer.listIterator(i).next().updateBias(learningRate);
		}

	}


	public double errorsAvg()
	{
		double avg = 0.0;

		for(int i = 0; i < outputSize;i++ )
		{
			avg += outputLayer.listIterator(i).next().getErrorFactor() *outputLayer.listIterator(i).next().getErrorFactor() ;
			
		}	

		return avg;
	}


	public double outputSum()
	{

		double sum = 0;

		for(int i = 0; i < outputSize;i++ )
		{
			sum += outputLayer.listIterator(i).next().getValue() ;
		}	

		return sum;
	}

	public void resetErrors()
	{
		for(int i = 0; i < outputSize;i++ )
		{
			outputLayer.listIterator(i).next().resetError();

		}	

		for(int i = 0; i < hiddenLayers.size(); i++)
		{
			for(int j = 0; j < hiddenLayers.listIterator(i).next().size(); j++)
			{

				hiddenLayers.listIterator(i).next().listIterator(j).next().resetError();
			}

		}

	}
	
	private ArrayList<Double[]> capitalsReader(FileReader f) {
		ArrayList<Double []> capitals = new ArrayList<Double []>();
		ArrayList<ArrayList<Double>> def = f.read();



		for(int i = 0; i < def.size(); i++)
		{
			boolean inArray = false;;
			Double coords[] = {def.listIterator(i).next().listIterator(def.listIterator(i).next().size()-2).next() , def.listIterator(i).next().listIterator(def.listIterator(i).next().size()-1).next() };
			for(int j = 0; j < capitals.size();j++)
			{
				if(capitals.listIterator(j).next()[0].equals(coords[0]) && capitals.listIterator(j).next()[1].equals(coords[1]) )
				{
					inArray = true;
					break;
				}

			}

			if(!inArray)
				capitals.add(coords);
		}
		return capitals;
	}

	public void Run(){

		FileReader f = new FileReader(filename);

		ArrayList<Double[]> capitals = capitalsReader(f);

		ArrayList<ArrayList<Double>> def = f.read();
		ArrayList<Double> errors = new ArrayList<Double>();

		for (int l = 0 ; l < 20; l++){
			
			/*
			if ( l == 799)
			{
				System.out.println("cenas");
			}
			*/
			
			errors.clear();
			for (int i = 0 ; i < def.size() ; i++){
				
				

				resetErrors();

				ArrayList<Double> inputs = new ArrayList<Double>();
				for(int k = 0; k < def.listIterator(i).next().size() - 2;k++)
					inputs.add(def.listIterator(i).next().listIterator(k).next());

				double normalInputs[] = new double[inputs.size()];
				
				for(int index = 0;index < inputs.size();index++)
					normalInputs[index] = inputs.listIterator(index).next();
				
				
				frontPropagation(normalInputs);

				double coords[] = {def.listIterator(i).next().listIterator(def.listIterator(i).next().size()-2).next() , def.listIterator(i).next().listIterator(def.listIterator(i).next().size()-1).next() };
				double expectedOutput[] = new double[33];

				int j = 0;

				for(; j < capitals.size();j++)
				{
					if(capitals.listIterator(j).next()[0].equals(coords[0]) && capitals.listIterator(j).next()[1].equals(coords[1]) )
						expectedOutput[j] = 1;
					else
						expectedOutput[j] = 0;
				}




				backPropagation(expectedOutput);

				errors.add(errorsAvg());

			}
		}

		double avgError = 0;
		

		for(int i = 0; i < errors.size();i++)
		{
			avgError += errors.listIterator(i).next();
		}

		avgError *= 1.0/(2*def.size());

		double outputsum = outputSum();
		System.out.println("error: " + avgError);
		System.out.println("output sum: "+ outputsum);

		
		//calcular media do erro
		// if erro << 0,0001  -> acabar
		// recome�ar do inicio


	}
	


	private double sigmoide(double netValue){

		return  (1.0) / (1.0 + Math.exp( -netValue));
	}

	public double[] ArrayListToArray(ArrayList<Double> Doubles)
	{
		double[] ret = new double[Doubles.size()];
		for (int i=0; i < ret.length; i++)
		{
			ret[i] = Doubles.get(i).doubleValue();
		}
		return ret;
	}

	public ArrayList<Neuron> getInputLayer() {
		return inputLayer;
	}

	public void setInputLayer(ArrayList<Neuron> inputLayer) {
		this.inputLayer = inputLayer;
	}



	public int getHiddenLayersNumber() {
		return hiddenLayersNumber;
	}


	public void setHiddenLayersNumber(int hiddenLayersNumber) {
		this.hiddenLayersNumber = hiddenLayersNumber;
	}


	public ArrayList<Integer> getHiddenSizes() {
		return hiddenSizes;
	}


	public void setHiddenSizes(ArrayList<Integer> hiddenSizes) {
		this.hiddenSizes = hiddenSizes;
	}


	public ArrayList<ArrayList<Neuron>> getHiddenLayers() {
		return hiddenLayers;
	}


	public void setHiddenLayers(ArrayList<ArrayList<Neuron>> hiddenLayers) {
		this.hiddenLayers = hiddenLayers;
	}


	public double getLearningRate() {
		return learningRate;
	}


	public void setLearningRate(double learningRate) {
		this.learningRate = learningRate;
	}


	public ArrayList<Neuron> getOutputLayer() {
		return outputLayer;
	}

	public void setOutputLayer(ArrayList<Neuron> outputLayer) {
		this.outputLayer = outputLayer;
	}

	public int getInputSize() {
		return inputSize;
	}

	public void setInputSize(int inputSize) {
		this.inputSize = inputSize;
	}

	public int getOutputSize() {
		return outputSize;
	}

	public void setOutputSize(int outputSize) {
		this.outputSize = outputSize;
	}

}
