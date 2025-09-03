const { ethers } = require('ethers');

async function testUSDC() {
  try {
    console.log('Testing USDC contract on Sepolia...');
    
    const provider = new ethers.JsonRpcProvider('https://ethereum-sepolia.publicnode.com');
    const usdcAddress = '0x1c7D4B196Cb0C7B01d743Fbc6116a902379C7238';
    const erc20Abi = [
      'function balanceOf(address) view returns (uint256)',
      'function decimals() view returns (uint8)',
      'function symbol() view returns (string)',
      'function name() view returns (string)'
    ];
    
    const contract = new ethers.Contract(usdcAddress, erc20Abi, provider);
    const yourWallet = '0x71D143277c05b1660AF20D9954ddE972dD4b4944';
    
    console.log('Testing contract methods...');
    
    try {
      const decimals = await contract.decimals();
      console.log('✓ USDC decimals:', decimals);
      
      const symbol = await contract.symbol();
      console.log('✓ USDC symbol:', symbol);
      
      const name = await contract.name();
      console.log('✓ USDC name:', name);
      
      const balance = await contract.balanceOf(yourWallet);
      console.log('✓ Your USDC balance:', ethers.formatUnits(balance, decimals));
      
    } catch (contractError) {
      console.error('✗ Contract call failed:', contractError.message);
      return false;
    }
    
    return true;
    
  } catch (error) {
    console.error('Error testing USDC:', error.message);
    return false;
  }
}

testUSDC().then(success => {
  if (success) {
    console.log('\n✅ USDC contract is working correctly!');
  } else {
    console.log('\n❌ USDC contract has issues');
  }
});
