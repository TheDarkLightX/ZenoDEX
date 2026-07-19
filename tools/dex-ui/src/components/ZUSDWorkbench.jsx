import './ZUSDWorkbench.css';
import ZUSDTauWalletSurface from './ZUSDTauWalletSurface.jsx';
import ZUSDMonetarySurface from './ZUSDMonetarySurface.jsx';

function ZUSDWorkbench() {
  return (
    <section className="zusd-workbench">
      <ZUSDMonetarySurface />
      <ZUSDTauWalletSurface />
    </section>
  );
}

export default ZUSDWorkbench;
