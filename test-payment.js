const { ethers } = require('ethers');

async function testPayment() {
  try {
    console.log('Testing USDC payment...');
    
    // Use your private key and RPC URL
    const privateKey = process.env.PRIVATE_KEY || '0xea2f646bfad534ba9d81b29d67242fc6dbcf49f37d5813e681a6ea4f5b4b700f';
    const provider = new ethers.JsonRpcProvider('https://ethereum-sepolia.publicnode.com');
    const wallet = new ethers.Wallet(privateKey, provider);
    
    console.log('Using wallet:', wallet.address);
    
    // USDC contract
    const usdcAddress = '0x1c7D4B196Cb0C7B01d743Fbc6116a902379C7238';
    const usdcAbi = [
      'function transfer(address to, uint256 amount) returns (bool)',
      'function balanceOf(address account) view returns (uint256)',
      'function decimals() view returns (uint8)',
      'function approve(address spender, uint256 amount) returns (bool)',
      'function allowance(address owner, address spender) view returns (uint256)'
    ];
    
    const contract = new ethers.Contract(usdcAddress, usdcAbi, wallet);
    
    // Check balance first
    const decimals = await contract.decimals();
    const balance = await contract.balanceOf(wallet.address);
    const balanceFormatted = ethers.formatUnits(balance, decimals);
    
    console.log('USDC Balance:', balanceFormatted);
    console.log('ETH Balance for gas:', ethers.formatEther(await provider.getBalance(wallet.address)));
    
    // Try a very small transfer to yourself (safe test)
    const amount = ethers.parseUnits('0.001', decimals);
    console.log('Attempting transfer of 0.001 USDC to self...');
    
    // Estimate gas first
    try {
      const gasEstimate = await contract.transfer.estimateGas(wallet.address, amount);
      console.log('Gas estimate:', gasEstimate.toString());
      
      const gasPrice = await provider.getFeeData();
      const estimatedCost = gasEstimate * gasPrice.gasPrice;
      console.log('Estimated cost:', ethers.formatEther(estimatedCost), 'ETH');
      
    } catch (estimateError) {
      console.error('❌ Gas estimation failed:', estimateError.message);
      if (estimateError.reason) {
        console.error('Reason:', estimateError.reason);
      }
      return false;
    }
    
    // Try the actual transfer
    try {
      const tx = await contract.transfer(wallet.address, amount, {
        gasLimit: 100000 // Set a gas limit to avoid out of gas errors
      });
      console.log('Transaction sent:', tx.hash);
      
      const receipt = await tx.wait();
      console.log('Transaction confirmed in block:', receipt.blockNumber);
      console.log('✅ Transfer successful!');
      
      return true;
      
    } catch (transferError) {
      console.error('❌ Transfer failed:', transferError.message);
      if (transferError.reason) {
        console.error('Reason:', transferError.reason);
      }
      if (transferError.code) {
        console.error('Error code:', transferError.code);
      }
      return false;
    }
    
  } catch (error) {
    console.error('Payment test failed:', error.message);
    return false;
  }
}

// Run the test
testPayment().then(success => {
  if (success) {
    console.log('\n✅ Payment test successful!');
  } else {
    console.log('\n❌ Payment test failed');
  }
});
